/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.RingTheory.HopfAlgebra.Cartier

/-!
# Cartier's theorem: group schemes in characteristic zero are smooth

**Cartier's theorem** states that every group scheme locally of finite type over a field `K` of
characteristic zero is reduced, and hence smooth over `K`.

A group scheme over `K` is a scheme `G` with a structure morphism `f : G ⟶ Spec K` making
`Over.mk f` a group object of the category of `K`-schemes, that is, carrying

```
  G ×_{Spec K} G --- mul ---> G <--- one --- Spec K
```

together with an inverse `G ⟶ G`, all of them morphisms over `Spec K`.

Mathlib provides `AlgebraicGeometry.smooth_of_grpObj`: a group scheme locally of finite type over
a field which is *geometrically* reduced is smooth over that field.  In characteristic zero the
base field is perfect, so reducedness and geometric reducedness agree; Mathlib does not yet have
that implication (`Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean` only goes the easy way),
so the smoothness half is stated separately below rather than derived here.

## Main statements

* `AlgebraicGeometry.GrpObj.exists_derivation_of_isOpenImmersion`: on an affine open subscheme
  `Spec A` of a group scheme, every tangent vector at a rational point extends to a derivation of
  `A` (invariant vector fields).
* `AlgebraicGeometry.isReduced_of_grpObj`: a group scheme locally of finite type over a field of
  characteristic zero is reduced.
* `AlgebraicGeometry.smooth_of_grpObj_of_charZero`: such a group scheme is smooth over the base
  field.

## Blueprint

`AlgebraicGeometry.isReduced_of_grpObj` and `AlgebraicGeometry.smooth_of_grpObj_of_charZero`
implement `proposition-cartier-s-theorem`.

The result is due to Cartier, *Questions de rationalité des diviseurs en géométrie algébrique*
(1958).
-/

@[expose] public section

open CategoryTheory Opposite TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

universe u

section InvariantDerivation

variable {K : Type u} [Field K]

/-- **Invariant vector fields.** Let `G` be a group scheme over a field `K` and let
`j : Spec A ⟶ G` be an affine open subscheme. Every tangent vector of `A` at a `K`-point `e` of
`A`, given as a linear form `φ` on the cotangent space `𝔪/𝔪²` at `e`, extends to a derivation `D`
of `A`.

Let `x` be the rational point of `G` given by `e` and `v : Spec K[ε] ⟶ G` the tangent vector.
The morphism `Φ : Spec A[ε] ⟶ G`, `(g, t) ↦ g x⁻¹ v(t)`, restricts to the inclusion `j` along
`Spec A ⟶ Spec A[ε]`; as `Spec A[ε]` and `Spec A` have the same points, `Φ` factors through
`j`, as `Spec ψ` for a section `ψ : A → A[ε]`, `ψ a = a + D(a) ε`, of the reduction modulo `ε`.
Evaluating at `x` recovers `v`, so `e ∘ D` is the derivation `φ`. -/
theorem GrpObj.exists_derivation_of_isOpenImmersion {G : Over (Spec (.of K))} [GrpObj G]
    {A : Type u} [CommRing A] [Algebra K A] (j : Spec (.of A) ⟶ G.left) [IsOpenImmersion j]
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap K A))) (e : A →ₐ[K] K)
    (φ : (RingHom.ker e).Cotangent →ₗ[K] K) :
    ∃ D : Derivation K A A, ∀ a (ha : a ∈ RingHom.ker e),
      e (D a) = φ ((RingHom.ker e).toCotangent ⟨a, ha⟩) := by
  let F := algSpec (CommRingCat.of K)
  let ob (R : Type u) [CommRing R] [Algebra K R] : Over (Spec (.of K)) :=
    F.obj (op (CommAlgCat.of K R))
  let hm {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
      (χ : R →ₐ[K] R') : ob R' ⟶ ob R :=
    F.map (CommAlgCat.ofHom χ).op
  have hm_comp {R R' R'' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
      [CommRing R''] [Algebra K R''] (χ : R →ₐ[K] R') (χ' : R' →ₐ[K] R'') :
      hm χ' ≫ hm χ = hm (χ'.comp χ) := by
    simp only [hm, ← F.map_comp, ← op_comp, CommAlgCat.ofHom_comp]
  have hm_id {R : Type u} [CommRing R] [Algebra K R] : hm (AlgHom.id K R) = 𝟙 _ := by
    simp only [hm, CommAlgCat.ofHom_id, op_id, F.map_id]
    rfl
  have hm_left {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
      (χ : R →ₐ[K] R') : (hm χ).left = Spec.map (CommRingCat.ofHom χ.toRingHom) := rfl
  let jO : ob A ⟶ G := Over.homMk j hj
  let τ := e.toDualNumber φ
  let c (R : Type u) [CommRing R] [Algebra K R] : ob R ⟶ G :=
    hm ((Algebra.ofId K R).comp e) ≫ jO
  have hc {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
      (χ : R →ₐ[K] R') : hm χ ≫ c R = c R' := by
    rw [← Category.assoc, hm_comp]
    congr 2
    ext a
    simp
  let v : ob (DualNumber K) ⟶ G := hm τ ≫ jO
  let pA : ob (DualNumber A) ⟶ G := hm (inlAlgHom K A A) ≫ jO
  let pT : ob (DualNumber A) ⟶ G := hm (DualNumber.mapAlgebraMap A) ≫ v
  let Φ : ob (DualNumber A) ⟶ G := pA * (c (DualNumber A))⁻¹ * pT
  have hi : hm (fstHom K A A) ≫ Φ = jO := by
    have h1 : hm (fstHom K A A) ≫ pA = jO := by
      rw [← Category.assoc, hm_comp]
      convert Category.id_comp jO
      convert hm_id
      ext a
      simp
    have h2 : hm (fstHom K A A) ≫ pT = c A := by
      simp only [pT, v, ← Category.assoc, hm_comp]
      congr 2
      ext a
      simp [τ]
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, h1, h2, hc, inv_mul_cancel_right]
  have he : hm (DualNumber.mapOfAlgHom e) ≫ Φ = v := by
    have h1 : hm (DualNumber.mapOfAlgHom e) ≫ pA = c (DualNumber K) := by
      rw [← Category.assoc, hm_comp]
      congr 2
      ext a
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
    have h2 : hm (DualNumber.mapOfAlgHom e) ≫ pT = v := by
      rw [← Category.assoc, hm_comp]
      convert Category.id_comp v
      convert hm_id
      ext <;> simp
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, h1, h2, hc, mul_inv_cancel, one_mul]
  -- every point of `Spec A[ε]` comes from `Spec A`, as `ε` is nilpotent
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (fstHom K A A).toRingHom)) := by
    intro (P : PrimeSpectrum (DualNumber A))
    refine ⟨PrimeSpectrum.comap (inlAlgHom K A A).toRingHom P, PrimeSpectrum.ext (Ideal.ext
      fun x ↦ ?_)⟩
    change DualNumber A at x
    have hn : (inr x.snd : DualNumber A) ∈ P.asIdeal :=
      (P.isPrime.mem_or_mem (by
        rw [DualNumber.mul_self_eq_zero_of_fst_eq_zero (fst_inr _ _)]
        exact zero_mem _)).elim id id
    have hx : inl x.fst = x - inr x.snd := by
      rw [eq_sub_iff_add_eq]
      exact inl_fst_add_inr_snd_eq x
    change inl x.fst ∈ P.asIdeal ↔ x ∈ P.asIdeal
    rw [hx]
    exact ⟨fun h ↦ by simpa using add_mem h hn, fun h ↦ sub_mem h hn⟩
  have hrange : Set.range Φ.left ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, (congrArg (fun φ : ob A ⟶ G ↦ φ.left z) hi).symm⟩
  let ψ : Spec (.of (DualNumber A)) ⟶ Spec (.of A) := IsOpenImmersion.lift j Φ.left hrange
  have hψ : ψ ≫ j = Φ.left := IsOpenImmersion.lift_fac _ _ _
  let ψ' := Spec.preimage ψ
  have hψ' : Spec.map ψ' = ψ := Spec.map_preimage ψ
  have h1 : ψ' ≫ CommRingCat.ofHom (fstHom K A A).toRingHom = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', Spec.map_id, ← cancel_mono j, Category.assoc, hψ, Category.id_comp,
      ← hm_left]
    exact congrArg Over.Hom.left hi
  have h2 : ψ' ≫ CommRingCat.ofHom (DualNumber.mapOfAlgHom e).toRingHom =
      CommRingCat.ofHom τ.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', ← cancel_mono j, Category.assoc, hψ, ← hm_left]
    exact congrArg Over.Hom.left he
  have h3 : CommRingCat.ofHom (algebraMap K A) ≫ ψ' =
      CommRingCat.ofHom (algebraMap K (DualNumber A)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', ← hj, ← Category.assoc, hψ]
    exact Over.w Φ
  let ψA : A →ₐ[K] DualNumber A :=
    { ψ'.hom with commutes' r := congr(($h3).hom r) }
  have hψA : (fstHom K A A).comp ψA = AlgHom.id K A := AlgHom.ext fun a ↦ congr(($h1).hom a)
  refine ⟨DualNumber.derivationOfSection ψA hψA, fun a ha ↦ ?_⟩
  have h2a : DualNumber.mapOfAlgHom e (ψA a) = τ a := congr(($h2).hom a)
  rw [DualNumber.derivationOfSection_apply, ← DualNumber.snd_mapOfAlgHom, h2a,
    AlgHom.snd_toDualNumber, AlgHom.cotangentDerivation_of_mem]


omit [Field K] in
theorem specMap_asOver_comp_specMap_asOver {K : Type u} [CommRing K] {R S T : Type u}
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (f : R →ₐ[K] S) (g : S →ₐ[K] T) :
    (Spec.map (CommRingCat.ofHom g.toRingHom)).asOver (Spec (.of K)) ≫
        (Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)) =
      (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)).asOver (Spec (.of K)) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **Invariant vector fields as infinitesimal right translations.** Let `G` be a group scheme over
a field `K`, `j : Spec A ⟶ G` an affine open subscheme and `v` a point of `G` over `K[ε]` reducing
to the identity modulo `ε`. The right translation `(g, t) ↦ g v(t)` of `Spec A` maps
`Spec A[ε]` into `Spec A`: it is `Spec ψ` for a section `ψ : A → A[ε]`, `ψ a = a + D(a) ε`, of
the reduction modulo `ε`, since `Spec A[ε]` and `Spec A` have the same points. -/
theorem GrpObj.exists_algHom_specMap_comp_eq_mul {G : Over (Spec (.of K))} [GrpObj G]
    {A : Type u} [CommRing A] [Algebra K A] (j : (Spec (.of A)).asOver (Spec (.of K)) ⟶ G)
    [IsOpenImmersion j.left] (v : (Spec (.of (DualNumber K))).asOver (Spec (.of K)) ⟶ G)
    (hv : (Spec.map (CommRingCat.ofHom (fstHom K K K).toRingHom)).asOver (Spec (.of K)) ≫ v = 1) :
    ∃ ψ : A →ₐ[K] DualNumber A, (fstHom K A A).comp ψ = AlgHom.id K A ∧
      (Spec.map (CommRingCat.ofHom ψ.toRingHom)).asOver (Spec (.of K)) ≫ j =
        ((Spec.map (CommRingCat.ofHom (inlAlgHom K A A).toRingHom)).asOver (Spec (.of K)) ≫ j) *
          ((Spec.map (CommRingCat.ofHom (DualNumber.mapAlgebraMap A).toRingHom)).asOver
            (Spec (.of K)) ≫ v) := by
  set Φ :=
    ((Spec.map (CommRingCat.ofHom (inlAlgHom K A A).toRingHom)).asOver (Spec (.of K)) ≫ j) *
    ((Spec.map (CommRingCat.ofHom (DualNumber.mapAlgebraMap A).toRingHom)).asOver
      (Spec (.of K)) ≫ v)
  have hi :
      (Spec.map (CommRingCat.ofHom (fstHom K A A).toRingHom)).asOver (Spec (.of K)) ≫ Φ = j := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specMap_asOver_comp_specMap_asOver,
      specMap_asOver_comp_specMap_asOver,
      show (fstHom K A A).comp (inlAlgHom K A A) = AlgHom.id K A from by ext; simp,
      show (fstHom K A A).comp (DualNumber.mapAlgebraMap A) =
        (Algebra.ofId K A).comp (fstHom K K K) from by ext; simp,
      ← specMap_asOver_comp_specMap_asOver, Category.assoc, hv, MonObj.comp_one, mul_one]
    convert Category.id_comp j
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
    exact Spec.map_id _
  -- every point of `Spec A[ε]` comes from `Spec A`, as `ε` is nilpotent
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (fstHom K A A).toRingHom)) := by
    intro (P : PrimeSpectrum (DualNumber A))
    refine ⟨PrimeSpectrum.comap (inlAlgHom K A A).toRingHom P, PrimeSpectrum.ext (Ideal.ext
      fun x ↦ ?_)⟩
    change DualNumber A at x
    have hn : (inr x.snd : DualNumber A) ∈ P.asIdeal :=
      (P.isPrime.mem_or_mem (by
        rw [DualNumber.mul_self_eq_zero_of_fst_eq_zero (fst_inr _ _)]
        exact zero_mem _)).elim id id
    have hx : inl x.fst = x - inr x.snd := by
      rw [eq_sub_iff_add_eq]
      exact inl_fst_add_inr_snd_eq x
    change inl x.fst ∈ P.asIdeal ↔ x ∈ P.asIdeal
    rw [hx]
    exact ⟨fun h ↦ by simpa using add_mem h hn, fun h ↦ sub_mem h hn⟩
  have hrange : Set.range Φ.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, (congrArg (fun φ : (Spec (.of A)).asOver (Spec (.of K)) ⟶ G ↦ φ.left z)
      hi).symm⟩
  let ψ : Spec (.of (DualNumber A)) ⟶ Spec (.of A) := IsOpenImmersion.lift j.left Φ.left hrange
  have hψ : ψ ≫ j.left = Φ.left := IsOpenImmersion.lift_fac _ _ _
  let ψ' := Spec.preimage ψ
  have hψ' : Spec.map ψ' = ψ := Spec.map_preimage ψ
  have h1 : ψ' ≫ CommRingCat.ofHom (fstHom K A A).toRingHom = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', Spec.map_id, ← cancel_mono j.left, Category.assoc, hψ,
      Category.id_comp]
    exact congrArg Over.Hom.left hi
  have hj : j.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    rw [Over.w j]
    simp [specOverSpec_over]
  have h3 : CommRingCat.ofHom (algebraMap K A) ≫ ψ' =
      CommRingCat.ofHom (algebraMap K (DualNumber A)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', ← hj, ← Category.assoc, hψ, Over.w Φ]
    simp [specOverSpec_over]
  let ψA : A →ₐ[K] DualNumber A :=
    { ψ'.hom with commutes' r := congr(($h3).hom r) }
  refine ⟨ψA, AlgHom.ext fun a ↦ congr(($h1).hom a), ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map ψ' ≫ j.left = Φ.left
  rw [hψ', hψ]
end InvariantDerivation

variable {K : Type u} [Field K] [CharZero K] {G : Scheme} (f : G ⟶ Spec (.of K))
  [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

include f in
/-- **Cartier's theorem** for affine group schemes: an affine group scheme of finite type over a
field of characteristic zero is reduced. Its coordinate ring is a finitely generated Hopf algebra,
reduced by `HopfAlgebra.isReduced_of_charZero`. (blueprint: `proposition-cartier-s-theorem`) -/
theorem isReduced_of_grpObj_of_isAffine [IsAffine G] : IsReduced G := by
  obtain ⟨H, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of K) (G := Grp.mk (Over.mk f))).2 ‹_›
  let e' : Spec (.of H.unop) ≅ G := (Grp.forget _ ⋙ Over.forget _).mapIso e
  have he : e'.hom ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K H.unop)) :=
    Over.w e.hom.hom.hom
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K H.unop))) := by
    rw [← he]
    infer_instance
  have : Algebra.FiniteType K H.unop := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.1 this
  have : _root_.IsReduced H.unop := HopfAlgebra.isReduced_of_charZero (k := K)
  exact isReduced_of_isOpenImmersion e'.inv

include f in
/-- **Cartier's theorem** over an algebraically closed field: a group scheme locally of finite type
over an algebraically closed field of characteristic zero is reduced.

Let `Spec A ⟶ G` be an affine open subscheme and `b` a nilpotent element of `A`. Every maximal
ideal of `A` is the kernel of a `K`-point `e`, and every tangent vector of `A` at `e` extends to a
derivation of `A` (`GrpObj.exists_derivation_of_isOpenImmersion`). By Cartier's lemma
(`AlgHom.exists_apply_eq_one_mul_eq_zero_of_forall_exists_derivation`) the annihilator of `b` is
not contained in the kernel of `e`. Hence it is the unit ideal and `b = 0`.
(blueprint: `proposition-cartier-s-theorem`) -/
theorem isReduced_of_grpObj_of_isAlgClosed [IsAlgClosed K] : IsReduced G := by
  have key (R : CommRingCat.{u}) (j : Spec R ⟶ G) [IsOpenImmersion j] : _root_.IsReduced R := by
    let : Algebra K R := (Spec.preimage (j ≫ f)).hom.toAlgebra
    have hj : j ≫ (Over.mk f).hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) :=
      (Spec.map_preimage (j ≫ f)).symm
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
      rw [← hj]
      exact inferInstanceAs (LocallyOfFiniteType (j ≫ f))
    have : Algebra.FiniteType K R := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
      exact RingHom.finiteType_algebraMap.1 this
    have := Algebra.FiniteType.isNoetherianRing K R
    refine ⟨fun b hb ↦ ?_⟩
    let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R b)
    by_cases hJ : J = ⊤
    · have h : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
      simpa [J] using h
    obtain ⟨M, hM, hJM⟩ := J.exists_le_maximal hJ
    obtain ⟨g, rfl⟩ := exists_algHom_ker_eq_of_isMaximal K R M
    obtain ⟨t, ht, htb⟩ := AlgHom.exists_apply_eq_one_mul_eq_zero_of_forall_exists_derivation
      (fun φ ↦ GrpObj.exists_derivation_of_isOpenImmersion (G := Over.mk f) (A := R) j hj g φ) hb
    have h := RingHom.mem_ker.1 (hJM (show t ∈ J by simpa [J] using htb))
    rw [ht] at h
    exact absurd h one_ne_zero
  let 𝒰 := G.affineOpenCover
  have (i : 𝒰.openCover.I₀) : IsReduced (𝒰.openCover.X i) := by
    have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have := key (𝒰.X i) (𝒰.f i)
    exact inferInstanceAs (IsReduced (Spec (𝒰.X i)))
  exact IsReduced.of_openCover G 𝒰.openCover

include f in
/-- A group scheme locally of finite type over a field of characteristic zero has no nilpotents
in its structure sheaf, i.e. it is reduced: its base change to an algebraic closure is reduced by
`isReduced_of_grpObj_of_isAlgClosed`, and reducedness descends along the faithfully flat
morphism `G_K̄ ⟶ G`. (blueprint: `proposition-cartier-s-theorem`) -/
theorem isReduced_of_grpObj : IsReduced G := by
  let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
  have : IsReduced (Limits.pullback f g) :=
    isReduced_of_grpObj_of_isAlgClosed (Limits.pullback.snd f g)
  have : IsSchemeTheoreticallyDominant g := .of_isDominant g
  exact IsSchemeTheoreticallyDominant.isReduced (Limits.pullback.fst f g)

/-- **Cartier's theorem**: a group scheme locally of finite type over a field of characteristic
zero is smooth over the base field, equivalently `dim Lie(G) = dim G`.
(blueprint: `proposition-cartier-s-theorem`) -/
theorem smooth_of_grpObj_of_charZero : Smooth f := by
  have : GeometricallyReduced f := by
    refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 fun L _ _ ↦ ?_⟩
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    let : GrpObj (Over.mk (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap K L))))) := Over.grpObjMkPullbackSnd
    exact isReduced_of_grpObj (Limits.pullback.snd f _)
  exact smooth_of_grpObj f

end AlgebraicGeometry
