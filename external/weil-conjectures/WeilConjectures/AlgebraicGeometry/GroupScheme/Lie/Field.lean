/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

/-!
# The Lie algebra of a group scheme of finite type over a field

The Lie algebra of a group scheme of finite type over a field.

## Main results

- `AlgebraicGeometry.GrpObj.finrank_lie_eq_finrank_cotangent`: in an affine chart `Spec A` at the
  identity, `Lie(G)` has the dimension of the cotangent space of `A` at the identity.
- `AlgebraicGeometry.GrpObj.exists_affine_chart`: such charts exist with `A` of finite type.
- `AlgebraicGeometry.GrpObj.finrank_lie_le_topologicalKrullDim`: in characteristic zero,
  `dim Lie(G) ≤ dim G`.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Group schemes of finite type over a field -/

section Field

variable {k : Type u} [Field k]

/-- A morphism of schemes locally of finite type over an algebraically closed field `k` which is
surjective on underlying spaces is surjective on `k`-points.

The point `y` is a section of `Y → Spec k`, hence a closed immersion, so the fibre
`X ×_Y Spec k` is a closed subscheme of `X`, nonempty since `f` is surjective and locally of finite
type over `k`; a closed point of it has residue field `k`, giving a `k`-point of `X` over `y`. -/
theorem exists_points_comp_eq_of_surjective [IsAlgClosed k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (hf : Function.Surjective f.left.base)
    (y : points Y k) : ∃ x : points X k, x ≫ f = y := by
  let g : Spec (.of k) ⟶ Y.left := y.left
  have hg : g ≫ Y.hom = 𝟙 (Spec (.of k)) := by
    rw [Over.w y]
    exact Spec.map_id _
  have := isClosedImmersion_of_comp_eq_id _ _ hg
  have hsnd : Limits.pullback.fst f.left g ≫ X.hom = Limits.pullback.snd f.left g := by
    rw [← Over.w f, Limits.pullback.condition_assoc, hg, Category.comp_id]
  have : LocallyOfFiniteType (Limits.pullback.snd f.left g) := by
    rw [← hsnd]
    infer_instance
  have := LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd f.left g)
  obtain ⟨x₀, hx₀⟩ := hf (g (IsLocalRing.closedPoint k))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x₀ _ hx₀
  obtain ⟨p, -, hp⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem (Set.mem_univ z))
    isClosed_univ.isLocallyClosed
  refine ⟨Over.homMk (pointOfClosedPoint (Limits.pullback.snd f.left g) p hp ≫
    Limits.pullback.fst f.left g) ?_, ?_⟩
  · rw [Category.assoc, hsnd, pointOfClosedPoint_comp]
    exact (Spec.map_id _).symm
  · ext1
    simp [Limits.pullback.condition, g]

/-! ### Affine charts at the identity

Let `j : Spec A ⟶ G` be an affine open subscheme of a group scheme `G` over `k` and `e` a
`k`-point of `A` such that `j ∘ Spec e` is the identity point. A tangent vector `v` of `G`, a point
of `G` over `k[ε]` reducing to the identity, factors through `j`, as `Spec ψ` for a point
`ψ : A → k[ε]` lifting `e`, and `ψ` is the composite of `A → 𝒪_{G,1}` with `v^♯`. Hence
`Lie(G)` is the dual of the cotangent space of `A` at `e`. -/

/-- For an open immersion `j : Spec A ⟶ X` and a point `x` of `Spec A`, the composite of
`A → 𝒪_{Spec A, x} ≅ 𝒪_{X, j x}` with the local homomorphism `𝒪_{X, j x} → R` of a point
`Spec ψ ≫ j` of `X` with values in a local ring `R` sending the closed point to `j x` is `ψ`. -/
theorem Scheme.germ_inv_stalkMap_stalkClosedPointTo {X : Scheme.{u}} {A R : CommRingCat.{u}}
    [IsLocalRing R] (j : Spec A ⟶ X) [IsOpenImmersion j] (x : Spec A) (ψ : A ⟶ R)
    (f : Spec R ⟶ X) (hf : f = Spec.map ψ ≫ j) (h : j x = f (IsLocalRing.closedPoint R)) :
    (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ x trivial ≫ inv (j.stalkMap x) ≫
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo f = ψ := by
  subst hf
  obtain rfl : x = Spec.map ψ (IsLocalRing.closedPoint R) := j.isOpenEmbedding.injective h
  have e : (X.presheaf.stalkCongr (.of_eq h)).hom = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [e, Category.id_comp, Scheme.stalkClosedPointTo_comp, IsIso.inv_hom_id_assoc,
    Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]

/-- A morphism `f : Spec R ⟶ X` from the spectrum of a local ring sending the closed point into
the image of an open immersion `j : Spec A ⟶ X` factors through `j`, as `Spec ψ ≫ j`. -/
theorem IsOpenImmersion.exists_eq_specMap_comp {X : Scheme.{u}} {A R : Type u} [CommRing A]
    [CommRing R] [IsLocalRing R] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (f : Spec (.of R) ⟶ X) (hf : f (IsLocalRing.closedPoint R) ∈ Set.range j) :
    ∃ ψ : A →+* R, f = Spec.map (CommRingCat.ofHom ψ) ≫ j := by
  have h : Set.range f ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open
      j.isOpenEmbedding.isOpen_range hf
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j f h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

namespace GrpObj

variable {G : Over (Spec (.of k))} [GrpObj G] {A : Type u} [CommRing A] [Algebra k A]
  (j : Spec (.of A) ⟶ G.left) [IsOpenImmersion j]

omit [GrpObj G] [IsOpenImmersion j] in
/-- If a point `p` of `G` with values in a `k`-algebra `R` factors through a chart
`j : Spec A ⟶ G` over `k` as `Spec ψ ≫ j`, then `ψ` is a `k`-algebra homomorphism. -/
theorem comp_algebraMap_of_left_eq {R : Type u} [CommRing R] [Algebra k R]
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) (p : points G R)
    (ψ : A →+* R) (hψ : p.left = Spec.map (CommRingCat.ofHom ψ) ≫ j) :
    ψ.comp (algebraMap k A) = algebraMap k R := by
  have h := Over.w p
  rw [hψ, Category.assoc, hj, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

omit [GrpObj G] [IsOpenImmersion j] in
/-- A `k`-algebra homomorphism `ψ : A → R` gives the point `Spec ψ ≫ j` of `G` with values in `R`
through a chart `j : Spec A ⟶ G` over `k`. -/
theorem exists_left_eq_specMap_comp {R : Type u} [CommRing R] [Algebra k R]
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) (ψ : A →ₐ[k] R) :
    ∃ p : points G R, p.left = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ j := by
  have h : ψ.toRingHom.comp (algebraMap k A) = algebraMap k R := ψ.comp_algebraMap
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ j) ?_, rfl⟩
  rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  rfl

omit [GrpObj G] in
/-- The base change of a point along `φ : R → S` is the precomposition with `Spec φ`. -/
theorem _root_.AlgebraicGeometry.points.map_left {R S : Type u} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S]
    (φ : R →ₐ[k] S) (p : points G R) :
    (points.map G φ p).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ p.left :=
  rfl

/-- The homomorphism `A → 𝒪_{G,1}` of an affine chart `j : Spec A ⟶ G` and a point `x` of
`Spec A` lying over the identity point. -/
noncomputable def chartStalkHom (x : Spec (.of A)) (hx : j x = onePoint G) :
    CommRingCat.of A ⟶ stalkOne G :=
  (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ x trivial ≫
    inv (j.stalkMap x) ≫ (G.left.presheaf.stalkCongr (.of_eq hx)).hom

variable {j}

omit [Algebra k A] in
/-- If a point `p` of `G` reducing to the identity factors through the chart `j` as `Spec ψ ≫ j`,
then `ψ` is the composite of `A → 𝒪_{G,1}` with `p^♯ : 𝒪_{G,1} → R`. -/
theorem kerHom_comp_chartStalkHom {x : Spec (.of A)} (hx : j x = onePoint G) {R : Type u}
    [CommRing R] [Algebra k R] [IsLocalRing R] {π : R →ₐ[k] k} [IsLocalHom π.toRingHom]
    (p : pointsKer G π) (ψ : A →+* R) (hψ : p.1.left = Spec.map (CommRingCat.ofHom ψ) ≫ j) :
    (kerHom p).comp (chartStalkHom j x hx).hom = ψ := by
  rw [kerHom, pointStalkHom, ← CommRingCat.hom_comp, chartStalkHom]
  simp only [Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]
  exact congrArg CommRingCat.Hom.hom (Scheme.germ_inv_stalkMap_stalkClosedPointTo j x _ _ hψ
    (hx.trans (closedPoint_eq_onePoint p.2).symm))

/-- The residue map of `𝒪_{G,1}` composed with `A → 𝒪_{G,1}` is the `k`-point `e` of the chart
lying over the identity. -/
theorem counit_comp_chartStalkHom {x : Spec (.of A)} (hx : j x = onePoint G) (e : A →ₐ[k] k)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left) :
    (counit G).comp (chartStalkHom j x hx).hom = e.toRingHom :=
  kerHom_comp_chartStalkHom hx (1 : pointsKer G (AlgHom.id k k)) _ he.symm

omit [Algebra k A] in
/-- A point of `G` reducing to the identity factors through the chart `j`. -/
theorem left_eq_specMap_comp {x : Spec (.of A)} (hx : j x = onePoint G) {R : Type u}
    [CommRing R] [Algebra k R] [IsLocalRing R] {π : R →ₐ[k] k} [IsLocalHom π.toRingHom]
    (p : pointsKer G π) :
    p.1.left = Spec.map (CommRingCat.ofHom ((kerHom p).comp (chartStalkHom j x hx).hom)) ≫ j := by
  obtain ⟨ψ, hψ⟩ := IsOpenImmersion.exists_eq_specMap_comp j p.1.left
    ⟨x, hx.trans (closedPoint_eq_onePoint p.2).symm⟩
  rwa [kerHom_comp_chartStalkHom hx p ψ hψ]

variable (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) {x : Spec (.of A)}
  (hx : j x = onePoint G)

/-- The point `A → k[ε]` lifting `e` of a tangent vector of `G`, through the chart `j`. -/
noncomputable def tangentChartHom (v : pointsKer G aug₁) : A →ₐ[k] DualNumber k :=
  { (kerHom v).comp (chartStalkHom j x hx).hom with
    commutes' c := RingHom.congr_fun
      (comp_algebraMap_of_left_eq j hj v.1 _ (left_eq_specMap_comp hx v)) c }

/-- `tangentChartHom` is the composite of `A → 𝒪_{G,1}` with `v^♯`. -/
theorem tangentChartHom_apply (v : pointsKer G aug₁) (a : A) :
    tangentChartHom hj hx v a = kerHom v (chartStalkHom j x hx a) :=
  rfl

/-- The point `A → k[ε]` of a tangent vector lifts the `k`-point `e` over the identity. -/
theorem fstHom_comp_tangentChartHom {e : A →ₐ[k] k}
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left)
    (v : pointsKer G aug₁) : (fstHom k k k).comp (tangentChartHom hj hx v) = e :=
  AlgHom.ext fun a ↦ (kerHom_apply_of_mem_ker v _).trans
    (RingHom.congr_fun (counit_comp_chartStalkHom hx e he) a)

/-- The rescaling of tangent vectors multiplies the `D_v` by the scalar. -/
theorem tangentCoeff_tangentScale (c : k) (v : pointsKer G aug₁) (a : stalkOne G) :
    tangentCoeff (tangentScale c v) a = c * tangentCoeff v a := by
  rw [tangentCoeff, kerHom_tangentMap]
  simp [TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

variable {e : A →ₐ[k] k}
  (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left)

/-- The linear form on the cotangent space at `e` of a tangent vector `v` is `a ↦ D_v(a)`. -/
theorem cotangentForm_tangentChartHom_toCotangent (v : pointsKer G aug₁) (a : RingHom.ker e) :
    e.cotangentForm (tangentChartHom hj hx v) (fstHom_comp_tangentChartHom hj hx he v)
      ((RingHom.ker e).toCotangent a) = tangentCoeff v (chartStalkHom j x hx a) :=
  rfl

/-- The linear form on the cotangent space of `A` at `e` of a tangent vector of `G`. -/
noncomputable def lieToDualCotangent : Lie G →ₗ[k] Module.Dual k (RingHom.ker e).Cotangent where
  toFun y := e.cotangentForm (tangentChartHom hj hx (lieEquivTangent G y))
    (fstHom_comp_tangentChartHom hj hx he _)
  map_add' y y' := by
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨a, rfl⟩ := (RingHom.ker e).toCotangent_surjective w
    rw [LinearMap.add_apply, cotangentForm_tangentChartHom_toCotangent hj hx he,
      cotangentForm_tangentChartHom_toCotangent hj hx he,
      cotangentForm_tangentChartHom_toCotangent hj hx he,
      lieEquivTangent_add, tangentCoeff_mul]
  map_smul' c y := by
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨a, rfl⟩ := (RingHom.ker e).toCotangent_surjective w
    rw [LinearMap.smul_apply, cotangentForm_tangentChartHom_toCotangent hj hx he,
      cotangentForm_tangentChartHom_toCotangent hj hx he, lieEquivTangent_smul,
      tangentCoeff_tangentScale, RingHom.id_apply, smul_eq_mul]

/-- The defining formula of `lieToDualCotangent`. -/
theorem lieToDualCotangent_apply (y : Lie G) :
    lieToDualCotangent hj hx he y = e.cotangentForm (tangentChartHom hj hx (lieEquivTangent G y))
      (fstHom_comp_tangentChartHom hj hx he _) :=
  rfl

/-- `lieToDualCotangent y` sends the class of `a ∈ ker e` to `D_v(a)`, `v` the tangent vector of
`y`. -/
theorem lieToDualCotangent_toCotangent (y : Lie G) (a : RingHom.ker e) :
    lieToDualCotangent hj hx he y ((RingHom.ker e).toCotangent a) =
      tangentCoeff (lieEquivTangent G y) (chartStalkHom j x hx a) :=
  rfl

/-- A tangent vector of `G` is determined by its linear form on the cotangent space at `e`, as it
factors through the chart `j`. -/
theorem lieToDualCotangent_injective : Function.Injective (lieToDualCotangent hj hx he) :=
  fun y y' h ↦ by
    have h' : tangentChartHom hj hx (lieEquivTangent G y) =
        tangentChartHom hj hx (lieEquivTangent G y') := by
      rw [← e.toDualNumber_cotangentForm _ (fstHom_comp_tangentChartHom hj hx he _),
        ← e.toDualNumber_cotangentForm (tangentChartHom hj hx (lieEquivTangent G y'))
          (fstHom_comp_tangentChartHom hj hx he _), ← lieToDualCotangent_apply hj hx he,
        ← lieToDualCotangent_apply hj hx he, h]
    have h'' : (kerHom (lieEquivTangent G y)).comp (chartStalkHom j x hx).hom =
        (kerHom (lieEquivTangent G y')).comp (chartStalkHom j x hx).hom :=
      RingHom.ext fun a ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, ← tangentChartHom_apply hj hx,
          ← tangentChartHom_apply hj hx, h']
    refine (lieEquivTangent G).injective (Subtype.ext (Over.OverMorphism.ext ?_))
    rw [left_eq_specMap_comp hx (lieEquivTangent G y),
      left_eq_specMap_comp hx (lieEquivTangent G y'), h'']

/-- Every linear form on the cotangent space at `e` comes from a tangent vector of `G`: the point
`Spec ψ ≫ j` for the corresponding point `ψ : A → k[ε]` lifting `e`. -/
theorem lieToDualCotangent_surjective : Function.Surjective (lieToDualCotangent hj hx he) :=
  fun φ ↦ by
    set ψ := e.toDualNumber φ
    obtain ⟨p, hpψ⟩ := exists_left_eq_specMap_comp j hj ψ
    have h : aug₁.toRingHom.comp ψ.toRingHom = e.toRingHom :=
      congrArg AlgHom.toRingHom (e.fstHom_comp_toDualNumber φ)
    have hp : p ∈ pointsKer G aug₁ := by
      rw [mem_pointsKer]
      refine Over.OverMorphism.ext ?_
      rw [points.map_left, hpψ, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, h, he]
    refine ⟨(lieEquivTangent G).symm ⟨p, hp⟩, LinearMap.ext fun w ↦ ?_⟩
    obtain ⟨a, rfl⟩ := (RingHom.ker e).toCotangent_surjective w
    have hψ := kerHom_comp_chartStalkHom hx ⟨p, hp⟩ ψ.toRingHom hpψ
    rw [lieToDualCotangent_toCotangent, Equiv.apply_symm_apply, tangentCoeff,
      ← RingHom.comp_apply, hψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.snd_toDualNumber, AlgHom.cotangentDerivation_of_mem φ a.2]

end GrpObj

namespace GrpObj

variable {G : Over (Spec (.of k))} [GrpObj G]

/-- **The Lie algebra in an affine chart.** Let `j : Spec A ⟶ G` be an affine open subscheme of a
group scheme `G` over `k` and `e` a `k`-point of `A` with `j ∘ Spec e` the identity point. Then
`Lie(G)` is the dual of the cotangent space of `A` at `e`: tangent vectors of `G` are the points
`A → k[ε]` lifting `e`, and the group law on them is the addition of point derivations. -/
theorem finrank_lie_eq_finrank_cotangent {A : Type u} [CommRing A] [Algebra k A]
    (j : Spec (.of A) ⟶ G.left) [IsOpenImmersion j]
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) (e : A →ₐ[k] k)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left) :
    Module.finrank k (Lie G) = Module.finrank k (RingHom.ker e).Cotangent := by
  have hx : j (Spec.map (CommRingCat.ofHom e.toRingHom) (IsLocalRing.closedPoint k)) =
      onePoint G := by
    rw [← Scheme.Hom.comp_apply, he]
    exact one_left_apply G _
  rw [(LinearEquiv.ofBijective (lieToDualCotangent hj hx he)
    ⟨lieToDualCotangent_injective hj hx he, lieToDualCotangent_surjective hj hx he⟩).finrank_eq,
    Subspace.dual_finrank_eq]

variable (G) in
/-- A group scheme locally of finite type over `k` has an affine chart `j : Spec A ⟶ G` around the
identity, with `A` a finitely generated `k`-algebra and a `k`-point `e` of `A` such that
`j ∘ Spec e` is the identity point. -/
theorem exists_affine_chart [LocallyOfFiniteType G.hom] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (j : Spec (.of A) ⟶ G.left)
      (_ : IsOpenImmersion j) (e : A →ₐ[k] k), Algebra.FiniteType k A ∧
      j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left := by
  obtain ⟨R, j, _, ⟨x, hx⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := onePoint G) (U := ⊤) trivial
  let : Algebra k R := (Spec.preimage (j ≫ G.hom)).hom.toAlgebra
  have hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
    (Spec.map_preimage (j ≫ G.hom)).symm
  obtain ⟨ψ, hψ⟩ := IsOpenImmersion.exists_eq_specMap_comp (A := R) j (1 : points G k).left
    ⟨x, hx.trans (one_left_apply G _).symm⟩
  let e : R →ₐ[k] k :=
    { ψ with commutes' c := RingHom.congr_fun (comp_algebraMap_of_left_eq j hj _ ψ hψ) c }
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
    rw [← hj]
    infer_instance
  have : Algebra.FiniteType k R := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.1 this
  exact ⟨R, _, _, j, inferInstance, e, this, hj, hψ.symm⟩

/-- **Lower bound in Cartier's dimension formula**: over a field of characteristic zero, the Lie
algebra of a group scheme `G` locally of finite type has dimension at most `dim G`. In an affine
chart `Spec A` at the identity, `Lie(G)` is dual to the cotangent space at the identity, every
tangent vector extends to an invariant derivation of `A`, and Cartier's lemma bounds the
dimension of the cotangent space by `dim A`. -/
theorem finrank_lie_le_topologicalKrullDim [CharZero k] [LocallyOfFiniteType G.hom] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) ≤ topologicalKrullDim G.left := by
  obtain ⟨A, _, _, j, _, e, _, hj, he⟩ := exists_affine_chart G
  rw [finrank_lie_eq_finrank_cotangent j hj e he]
  calc (Module.finrank k (RingHom.ker e).Cotangent : WithBot ℕ∞) ≤ ringKrullDim A :=
        AlgHom.finrank_cotangent_le_ringKrullDim
          (exists_derivation_of_isOpenImmersion (G := G) j hj e)
    _ = topologicalKrullDim (Spec (.of A)) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).symm
    _ ≤ topologicalKrullDim G.left := j.isOpenEmbedding.isInducing.topologicalKrullDim_le

end GrpObj

namespace GrpObj

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The Lie algebra of a group scheme of finite type over a field only sees the identity
component: the differential of the open immersion `G° ⟶ G` is bijective.
(blueprint: `proposition-cartier-s-theorem`) -/
theorem differential_identityComponentι_bijective :
    Function.Bijective (differential (identityComponentι G)) :=
  differential_bijective_of_isOpenImmersion (identityComponentι G)

/-- The Lie algebra of a group scheme of finite type over a field is the Lie algebra of its
identity component. (blueprint: `proposition-cartier-s-theorem`) -/
noncomputable def lieEquivIdentityComponent : Lie (identityComponent G) ≃ₗ⁅k⁆ Lie G :=
  lieEquivOfIsOpenImmersion (identityComponentι G)

end GrpObj

end Field

end AlgebraicGeometry
