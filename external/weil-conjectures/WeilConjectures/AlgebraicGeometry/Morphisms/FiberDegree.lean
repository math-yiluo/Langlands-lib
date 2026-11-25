/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.RingTheory.Flat.LocallyFree
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.Mathlib.RingTheory.Etale.FiberDegree
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# The degree of the fibre of an affine morphism at a point

For an affine morphism `g : U ⟶ X` and a point `x : X`, the scheme-theoretic fibre `g.fiber x`
is an affine scheme over `Spec κ(x)`, and we define `g.fiberDegree x` as the `κ(x)`-dimension
of its ring of global sections.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.ΓAlgebra`: for `h : Z ⟶ Spec R`, the ring of global sections
  of `Z` as an `R`-algebra.
- `AlgebraicGeometry.Scheme.Hom.finrankΓ`: the `R`-dimension of that algebra. For a finite
  group scheme over a field this is its order.
- `AlgebraicGeometry.Scheme.Hom.overHomEquivAlgHom`: for `Z` affine over `Spec R`, the points
  `Spec L ⟶ Z` over `Spec R` are the `R`-algebra homomorphisms `Γ(Z, ⊤) →ₐ[R] L`.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree`: the degree of the fibre of an affine morphism
  at a point.
- `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`: finite locally free morphisms, and
  those of constant fibre degree `d`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.finrankΓ_eq_of_iso`: `finrankΓ` is invariant under an
  isomorphism of schemes over an isomorphism of affine bases.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isPullback`: the fibre degree is invariant under
  base change.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isIso`: an isomorphism has fibre degree `1`.
- `AlgebraicGeometry.Scheme.Hom.isEmpty_of_forall_fiberDegree_eq_zero`: an étale morphism all of
  whose fibre degrees vanish has empty source.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isCompl`: the fibre degree is additive in
  complementary open (and closed) subschemes of the source.
- `AlgebraicGeometry.Scheme.Hom.exists_overIso_sigma_of_isSepClosed`: the fibre of a finite
  étale morphism over a separably closed point is a finite disjoint union of copies of the point.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_SpecMap`: comparison with the ring-theoretic
  `Ideal.fiberDegree`.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_morphismRestrict`: compatibility with restriction
  to an open of the target.
- `AlgebraicGeometry.fiberDegree_eq_finrankΓ`: over a field, the fibre degree of an affine
  morphism is the dimension of its ring of global sections.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_genericPoint`: the fibre of a quasi-finite affine
  morphism from an integral scheme through the generic point `η` has degree `[κ(η) : κ(f η)]`.
- `AlgebraicGeometry.Scheme.Hom.flat_of_fiberDegree_eq`,
  `AlgebraicGeometry.Scheme.Hom.finrank_eq_of_fiberDegree_eq`: a finite morphism of finite
  presentation to a reduced scheme with constant fibre degree `n` is flat of rank `n`.
- `AlgebraicGeometry.Scheme.Hom.eventually_fiberDegree_le`: the fibre degree of a finite morphism
  is upper semicontinuous.
- `AlgebraicGeometry.Scheme.Hom.flat_of_fiberDegree_eq_of_isClosed`,
  `AlgebraicGeometry.Scheme.Hom.finrank_eq_of_fiberDegree_eq_of_isClosed`: over a reduced Jacobson
  scheme it suffices that the fibres over closed points have degree `n`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Topology

namespace AlgebraicGeometry

section ΓAlgebra

variable {Z : Scheme.{u}} {R : CommRingCat.{u}}

/-- For `h : Z ⟶ Spec R`, the ring of global sections of `Z` as an `R`-algebra. -/
@[instance_reducible]
noncomputable def Scheme.Hom.ΓAlgebra (h : Z ⟶ Spec R) : Algebra R Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom.toAlgebra

lemma Scheme.Hom.algebraMap_ΓAlgebra (h : Z ⟶ Spec R) :
    letI := h.ΓAlgebra
    algebraMap R Γ(Z, ⊤) = ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom :=
  rfl

/-- The `R`-dimension of the ring of global sections of a scheme over `Spec R`.

For a finite group scheme `G` over a field `K` this is its *order* `|G| = dim_K Γ(G, 𝒪_G)`. -/
noncomputable def Scheme.Hom.finrankΓ (h : Z ⟶ Spec R) : ℕ :=
  letI := h.ΓAlgebra
  Module.finrank R Γ(Z, ⊤)

/-- An isomorphism of schemes over an isomorphism of affine bases induces an isomorphism of
rings of global sections compatible with the algebra structures. -/
lemma Scheme.Hom.finrankΓ_eq_of_iso {Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}}
    (h : Z ⟶ Spec R) (h' : Z' ⟶ Spec R') (e : Z ≅ Z') (i : R ≅ R')
    (he : e.hom ≫ h' ≫ Spec.map i.hom = h) :
    h.finrankΓ = h'.finrankΓ := by
  let _ := h.ΓAlgebra
  let _ := h'.ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv i.commRingCatIsoToRingEquiv
    (asIso e.inv.appTop).commRingCatIsoToRingEquiv ?_
  have he' : e.inv ≫ h = h' ≫ Spec.map i.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  change ((ΓSpecIso R').inv ≫ h'.appTop).hom.comp i.hom.hom =
    e.inv.appTop.hom.comp ((ΓSpecIso R).inv ≫ h.appTop).hom
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop, he',
    Scheme.Hom.comp_appTop, ← ΓSpecIso_inv_naturality_assoc]

/-- The spectrum of a field `k` has `dim_k Γ(Spec k, 𝒪) = 1`. -/
lemma Scheme.Hom.finrankΓ_id {k : Type u} [Field k] : Hom.finrankΓ (𝟙 (Spec (.of k))) = 1 := by
  let := Hom.ΓAlgebra (𝟙 (Spec (.of k)))
  have hb : Function.Bijective (algebraMap (CommRingCat.of k) Γ(Spec (.of k), ⊤)) := by
    rw [Hom.algebraMap_ΓAlgebra, Hom.id_appTop, Category.comp_id]
    exact ConcreteCategory.bijective_of_isIso _
  exact (AlgEquiv.ofBijective (Algebra.ofId (CommRingCat.of k) _) hb).toLinearEquiv.finrank_eq.symm
    |>.trans (Module.finrank_self k)

/-- The `R`-dimension of the global sections of `Spec S` over `Spec R` is `dim_R S`. -/
lemma Scheme.Hom.finrankΓ_SpecMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrankΓ = Module.finrank R S := by
  let _ := (Spec.map (CommRingCat.ofHom (algebraMap R S))).ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv ?_
  refine RingHom.ext fun y ↦ ?_
  change algebraMap R S y = (Scheme.ΓSpecIso (.of S)).hom
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop) y)
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

section BaseChange

variable {Y X : Scheme.{u}} {K L : CommRingCat.{u}} (ψ : K ⟶ L)
  {q : Y ⟶ X} {iY : Y ⟶ Spec L} {iX : X ⟶ Spec K} (H : IsPullback q iY iX (Spec.map ψ))
  [IsAffine X]

include H in
/-- For a pullback square of affine schemes over `Spec K ← Spec L`, the ring of global
sections of the top-left corner is the base change of that of the top-right corner. -/
lemma Scheme.Hom.nonempty_algEquiv_tensorProduct_Γ_of_isPullback :
    letI := iX.ΓAlgebra
    letI := iY.ΓAlgebra
    letI := ψ.hom.toAlgebra
    Nonempty (L ⊗[K] Γ(X, ⊤) ≃ₐ[L] Γ(Y, ⊤)) := by
  let _ := iX.ΓAlgebra
  let _ := iY.ΓAlgebra
  let _ := ψ.hom.toAlgebra
  have hUST : (⊤ : (Spec L).Opens) ≤ (Spec.map ψ) ⁻¹ᵁ ⊤ := le_top
  have hUSX : (⊤ : X.Opens) ≤ iX ⁻¹ᵁ ⊤ := le_top
  have hUY : (⊤ : Y.Opens) = q ⁻¹ᵁ ⊤ ⊓ iY ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) (isAffineOpen_top _)
  have P := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hiso
  simp only [Scheme.Hom.appLE_top_top] at P
  -- Precompose with the identifications `Γ(Spec K, ⊤) ≅ K` and `Γ(Spec L, ⊤) ≅ L`.
  have P' : IsPushout (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap K L))
      q.appTop (CommRingCat.ofHom (algebraMap L Γ(Y, ⊤))) := by
    refine P.of_iso (Scheme.ΓSpecIso K) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.algebraMap_ΓAlgebra]
    · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
      exact Scheme.ΓSpecIso_naturality ψ
    · simp
    · simp [Scheme.Hom.algebraMap_ΓAlgebra]
  have T := CommRingCat.isPushout_tensorProduct K L Γ(X, ⊤)
  let e : CommRingCat.of (L ⊗[K] Γ(X, ⊤)) ≅ Γ(Y, ⊤) := T.isoPushout ≪≫ P'.flip.isoPushout.symm
  have he : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom =
      CommRingCat.ofHom (algebraMap L Γ(Y, ⊤)) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inl_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
  refine ⟨AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun l ↦ ?_⟩
  change e.hom (algebraMap L (L ⊗[K] Γ(X, ⊤)) l) = algebraMap L Γ(Y, ⊤) l
  exact congr($(he).hom l)

end BaseChange

end ΓAlgebra

section Points

variable {Z : Scheme.{u}} {R : CommRingCat.{u}}

/-- A morphism `Spec L ⟶ Z` to an affine scheme is `Spec` of its action on global sections. -/
lemma Scheme.Spec_map_appTop_comp_ΓSpecIso_hom {L : CommRingCat.{u}} [IsAffine Z]
    (v : Spec L ⟶ Z) : Spec.map (v.appTop ≫ (Scheme.ΓSpecIso L).hom) = v ≫ Z.isoSpec.hom := by
  rw [← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom, Spec.map_comp]

/-- A morphism from an affine scheme to `Spec R` is `Spec` of its action on global sections. -/
lemma Scheme.Hom.isoSpec_inv_comp [IsAffine Z] (h : Z ⟶ Spec R) :
    Z.isoSpec.inv ≫ h = Spec.map ((Scheme.ΓSpecIso R).inv ≫ h.appTop) := by
  rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

/-- For `h : Z ⟶ Spec R` with `Z` affine and an `R`-algebra `L`, the morphisms `Spec L ⟶ Z`
over `Spec R` are the `R`-algebra homomorphisms `Γ(Z, ⊤) →ₐ[R] L`. -/
noncomputable def Scheme.Hom.overHomEquivAlgHom (h : Z ⟶ Spec R) [IsAffine Z] (L : Type u)
    [CommRing L] [Algebra R L] :
    letI := h.ΓAlgebra
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ Over.mk h) ≃
      (Γ(Z, ⊤) →ₐ[R] L) :=
  letI := h.ΓAlgebra
  { toFun u :=
      { toRingHom := (u.left.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom
        commutes' r := by
          have hu : u.left ≫ h = Spec.map (CommRingCat.ofHom (algebraMap R L)) := Over.w u
          change ((Scheme.ΓSpecIso R).inv ≫ h.appTop ≫ u.left.appTop ≫
            (Scheme.ΓSpecIso (.of L)).hom).hom r = _
          rw [← Scheme.Hom.comp_appTop_assoc, hu, Scheme.ΓSpecIso_naturality]
          exact congrArg (algebraMap R L) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso R) r) }
    invFun g := Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Z.isoSpec.inv) (by
      simp only [Over.mk_left, Over.mk_hom, Category.assoc, h.isoSpec_inv_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact g.commutes r)
    left_inv u := by
      ext1
      change Spec.map _ ≫ Z.isoSpec.inv = u.left
      rw [Iso.comp_inv_eq]
      exact Scheme.Spec_map_appTop_comp_ΓSpecIso_hom (Z := Z) u.left
    right_inv g := by
      ext1 x
      have := Scheme.Spec_map_appTop_comp_ΓSpecIso_hom
        (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Z.isoSpec.inv)
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
      exact congr($(Spec.map_injective this).hom x) }

/-- The bijection `Scheme.Hom.overHomEquivAlgHom` is natural in the algebra `L`. -/
lemma Scheme.Hom.overHomEquivAlgHom_comp (h : Z ⟶ Spec R) [IsAffine Z] {L L' : Type u}
    [CommRing L] [Algebra R L] [CommRing L'] [Algebra R L'] [Algebra L L']
    [IsScalarTower R L L']
    (v : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L'))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hv : v.left = Spec.map (CommRingCat.ofHom (algebraMap L L')))
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ Over.mk h) :
    letI := h.ΓAlgebra
    h.overHomEquivAlgHom L' (v ≫ u) =
      (IsScalarTower.toAlgHom R L L').comp (h.overHomEquivAlgHom L u) := by
  let := h.ΓAlgebra
  ext x
  change ((v.left ≫ u.left).appTop ≫ (Scheme.ΓSpecIso (.of L')).hom).hom x = _
  rw [hv, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

/-- If `Z` is affine and étale over a field `K`, then `Γ(Z, ⊤)` is an étale `K`-algebra. -/
lemma Scheme.Hom.etale_ΓAlgebra {K : Type u} [Field K] (h : Z ⟶ Spec (.of K)) [IsAffine Z]
    [Etale h] :
    letI := h.ΓAlgebra
    Algebra.Etale K Γ(Z, ⊤) := by
  let := h.ΓAlgebra
  have h' := HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := h) |>.mp inferInstance
  refine RingHom.etale_algebraMap.mp ?_
  rw [h.algebraMap_ΓAlgebra, CommRingCat.hom_comp, RingHom.Etale.respectsIso.cancel_left_isIso]
  exact h'

/-- An affine scheme `Z` over `Spec R` is étale over `Spec R` if and only if `Γ(Z, ⊤)` is an
étale `R`-algebra. -/
lemma Scheme.Hom.etale_iff_etale_ΓAlgebra (h : Z ⟶ Spec R) [IsAffine Z] :
    Etale h ↔
      letI := h.ΓAlgebra
      Algebra.Etale R Γ(Z, ⊤) := by
  let := h.ΓAlgebra
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), ← RingHom.etale_algebraMap,
    h.algebraMap_ΓAlgebra, CommRingCat.hom_comp, RingHom.Etale.respectsIso.cancel_left_isIso]

end Points

section GeometricFiber

/-- **The geometric fibre of a finite étale cover.** Let `f: P ⟶ Y` be finite étale and
`y: Spec k ⟶ Y` a point with `k` separably closed. Then the fibre `P ×_Y Spec k` is, as a
scheme over `Spec k`, a finite disjoint union of copies of `Spec k`, the number of copies being the
`k`-dimension of its ring of global sections. -/
theorem Scheme.Hom.exists_overIso_sigma_of_isSepClosed {P Y : Scheme.{u}} (f : P ⟶ Y)
    [IsFinite f] [Etale f] {k : Type u} [Field k] [IsSepClosed k] (y : Spec (.of k) ⟶ Y) :
    ∃ (ι : Type u) (_ : Finite ι), Nat.card ι = (pullback.snd f y).finrankΓ ∧
      Nonempty (Over.mk (pullback.snd f y) ≅
        Over.mk (Sigma.desc fun _ : ι ↦ 𝟙 (Spec (.of k)))) := by
  set h := pullback.snd f y
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom h
  let := h.ΓAlgebra
  have := h.etale_ΓAlgebra
  let A := Γ(pullback f y, ⊤)
  have := Algebra.Etale.finite_primeSpectrum k A
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed k A
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    e.symm.toRingEquiv.toCommRingCatIso.isIso_hom
  refine ⟨PrimeSpectrum A, inferInstance,
    (Algebra.Etale.finrank_eq_natCard_primeSpectrum k A).symm, ⟨Over.isoMk
      ((pullback f y).isoSpec ≪≫ asIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) ≪≫
        (asIso (sigmaSpec fun _ : PrimeSpectrum A ↦ CommRingCat.of k)).symm) ?_⟩⟩
  simp only [Over.mk_left, Over.mk_hom, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, ← sigmaSpec_comp_Spec_map_algebraMap, IsIso.inv_hom_id_assoc]
  rw [← Spec.map_comp, ← Iso.eq_inv_comp, h.isoSpec_inv_comp]
  congr 1
  ext r
  exact e.symm.commutes r

end GeometricFiber

section FiberDegree

variable {U X : Scheme.{u}} (g : U ⟶ X) [IsAffineHom g] (x : X)

/-- The ring of global sections of the fibre `g.fiber x` as a `κ(x)`-algebra. -/
noncomputable instance Scheme.Hom.fiberAlgebra : Algebra (X.residueField x) Γ(g.fiber x, ⊤) :=
  (g.fiberToSpecResidueField x).ΓAlgebra

omit [IsAffineHom g] in
lemma Scheme.Hom.algebraMap_fiber :
    algebraMap (X.residueField x) Γ(g.fiber x, ⊤) =
      ((Scheme.ΓSpecIso _).inv ≫ (g.fiberToSpecResidueField x).appTop).hom :=
  rfl

/-- The degree of the fibre of the affine morphism `g` at `x`: the dimension over `κ(x)` of the
ring of global sections of the (affine) scheme-theoretic fibre. -/
noncomputable def Scheme.Hom.fiberDegree : ℕ :=
  Module.finrank (X.residueField x) Γ(g.fiber x, ⊤)

/-- The fibre degree is invariant under base change. -/
lemma Scheme.Hom.fiberDegree_of_isPullback {U' X' : Scheme.{u}} {g' : U' ⟶ X'} [IsAffineHom g']
    {π' : U' ⟶ U} {π : X' ⟶ X} (h : IsPullback π' g' g π) (x' : X') :
    g'.fiberDegree x' = g.fiberDegree (π x') := by
  let _ := (π.residueFieldMap x').hom.toAlgebra
  obtain ⟨e⟩ := Scheme.Hom.nonempty_algEquiv_tensorProduct_Γ_of_isPullback
    (π.residueFieldMap x') (isPullback_fiberToSpecResidueField_of_isPullback h x')
  have e' : (X'.residueField x') ⊗[X.residueField (π x')] Γ(g.fiber (π x'), ⊤)
      ≃ₐ[X'.residueField x'] Γ(g'.fiber x', ⊤) := e
  change Module.finrank _ _ = Module.finrank _ _
  rw [← e'.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

instance (V : X.Opens) : IsAffineHom (g ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V

/-- The fibre degree is compatible with restriction to an open of the target. -/
lemma Scheme.Hom.fiberDegree_morphismRestrict (V : X.Opens) (x : V) :
    (g ∣_ V).fiberDegree x = g.fiberDegree x :=
  g.fiberDegree_of_isPullback (isPullback_morphismRestrict g V).flip x

section Etale

/-- The fibre of an étale morphism is a finite algebra over the residue field. -/
lemma Scheme.Hom.etale_Γ_fiber [Etale g] : Algebra.Etale (X.residueField x) Γ(g.fiber x, ⊤) := by
  have : Etale (g.fiberToSpecResidueField x) := MorphismProperty.pullback_snd _ _ inferInstance
  have h := HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := g.fiberToSpecResidueField x)
    |>.mp this
  change RingHom.Etale (algebraMap (X.residueField x) Γ(g.fiber x, ⊤))
  rw [Scheme.Hom.algebraMap_fiber, CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso]
  exact h

instance Scheme.Hom.finite_Γ_fiber [Etale g] :
    Module.Finite (X.residueField x) Γ(g.fiber x, ⊤) := by
  have := g.etale_Γ_fiber x
  exact Algebra.FormallyUnramified.finite_of_free _ _

omit [IsAffineHom g] in
/-- An isomorphism has fibre degree one. -/
lemma Scheme.Hom.fiberDegree_of_isIso [IsIso g] : g.fiberDegree x = 1 := by
  have : IsIso (g.fiberToSpecResidueField x) :=
    inferInstanceAs (IsIso (pullback.snd g (X.fromSpecResidueField x)))
  have h := Scheme.Hom.finrankΓ_eq_of_iso (g.fiberToSpecResidueField x) (𝟙 _)
    (asIso (g.fiberToSpecResidueField x)) (Iso.refl _) (by simp)
  refine h.trans ?_
  let _ := Scheme.Hom.ΓAlgebra (𝟙 (Spec (X.residueField x)))
  rw [Scheme.Hom.finrankΓ, Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv (S₁ := X.residueField x) ?_,
    Module.finrank_self]
  refine RingHom.ext fun y ↦ ?_
  change y = (Scheme.ΓSpecIso (X.residueField x)).hom
    (((Scheme.ΓSpecIso (X.residueField x)).inv ≫
      Scheme.Hom.appTop (𝟙 (Spec (X.residueField x)))) y)
  simp

omit [IsAffineHom g] in
/-- If `U` is empty, all fibre degrees vanish. -/
lemma Scheme.Hom.fiberDegree_of_isEmpty [IsEmpty U] : g.fiberDegree x = 0 := by
  have : IsEmpty (g.fiber x) := Function.isEmpty (g.fiberι x)
  exact Module.finrank_zero_of_subsingleton

/-- An étale morphism all of whose fibre degrees vanish has empty source. -/
lemma Scheme.Hom.isEmpty_of_forall_fiberDegree_eq_zero [Etale g]
    (h : ∀ x, g.fiberDegree x = 0) : IsEmpty U := by
  refine ⟨fun u ↦ ?_⟩
  have hsub : Subsingleton Γ(g.fiber (g u), ⊤) := Module.finrank_zero_iff.mp (h (g u))
  have : IsEmpty (Spec Γ(g.fiber (g u), ⊤)) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum Γ(g.fiber (g u), ⊤)))
  exact this.false ((g.fiber (g u)).isoSpec.hom (g.asFiber u))

end Etale

section IsCompl

/-- For complementary opens `O₁ O₂` of a scheme `Z`, restriction identifies `Γ(Z, ⊤)` with
`Γ(Z, O₁) × Γ(Z, O₂)`. -/
lemma Scheme.bijective_restrict_prod_of_isCompl (Z : Scheme.{u}) {O₁ O₂ : Z.Opens}
    (h : IsCompl O₁ O₂) :
    Function.Bijective (RingHom.prod (Z.presheaf.map (homOfLE (le_top : O₁ ≤ ⊤)).op).hom
      (Z.presheaf.map (homOfLE (le_top : O₂ ≤ ⊤)).op).hom) := by
  have hinf : O₁ ⊓ O₂ = ⊥ := h.inf_eq_bot
  have hsup : O₁ ⊔ O₂ = ⊤ := h.sup_eq_top
  let c := Z.sheaf.isProductOfDisjoint O₁ O₂ hinf
  let e := c.conePointUniqueUpToIso (CommRingCat.prodFanIsLimit Γ(Z, O₁) Γ(Z, O₂))
  have he : e.hom = CommRingCat.ofHom (RingHom.prod
      (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom
      (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom) := rfl
  have hbij : Function.Bijective (RingHom.prod
      (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom
      (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom) := by
    have := ConcreteCategory.bijective_of_isIso e.hom
    rw [he] at this
    exact this
  have hbij' : Function.Bijective (fun s : Γ(Z, ⊤) ↦
      ((Z.presheaf.map (eqToHom hsup).op).hom s : Γ(Z, O₁ ⊔ O₂))) :=
    ConcreteCategory.bijective_of_isIso (Z.presheaf.map (eqToHom hsup).op)
  have key := hbij.comp hbij'
  have e₁ : Z.presheaf.map (homOfLE (le_top : O₁ ≤ ⊤)).op =
      Z.presheaf.map (eqToHom hsup).op ≫ Z.presheaf.map (homOfLE le_sup_left).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  have e₂ : Z.presheaf.map (homOfLE (le_top : O₂ ≤ ⊤)).op =
      Z.presheaf.map (eqToHom hsup).op ≫ Z.presheaf.map (homOfLE le_sup_right).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  convert key using 1
  ext s
  · exact congr($(e₁) s)
  · exact congr($(e₂) s)

variable {V₁ V₂ : U.Opens} (h : IsCompl V₁ V₂)

include h in
/-- Each of two complementary opens is closed. -/
lemma isClosedImmersion_ι_of_isCompl_left : IsClosedImmersion V₁.ι := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.Opens.range_ι]
  have h1 : ∀ x, x ∈ V₁ → x ∉ V₂ := fun x hx hx' ↦ by
    have : x ∈ V₁ ⊓ V₂ := ⟨hx, hx'⟩
    rw [h.inf_eq_bot] at this
    exact this
  have h2 : ∀ x, x ∉ V₂ → x ∈ V₁ := fun x hx ↦ by
    have : x ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; trivial
    exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_right hx
  have : (V₁ : Set U) = (V₂ : Set U)ᶜ := Set.ext fun x ↦ ⟨h1 x, h2 x⟩
  rw [this]
  exact isClosed_compl_iff.mpr V₂.isOpen

include h in
/-- Each of two complementary opens is closed. -/
lemma isClosedImmersion_ι_of_isCompl_right : IsClosedImmersion V₂.ι :=
  isClosedImmersion_ι_of_isCompl_left h.symm

/-- The fibre of the restriction of `g` to an open `V ⊆ U` is the corresponding open of the
fibre of `g`, compatibly with the structure maps to `Spec κ(x)`. -/
noncomputable def Scheme.Hom.fiberRestrictIso (V : U.Opens) :
    (V.ι ≫ g).fiber x ≅ ((g.fiberι x) ⁻¹ᵁ V).toScheme :=
  (pullbackRightPullbackFstIso g (X.fromSpecResidueField x) V.ι).symm ≪≫
    pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict (g.fiberι x) V

omit [IsAffineHom g] in
lemma Scheme.Hom.fiberRestrictIso_hom_ι_fiberToSpecResidueField (V : U.Opens) :
    (g.fiberRestrictIso x V).hom ≫ ((g.fiberι x) ⁻¹ᵁ V).ι ≫ g.fiberToSpecResidueField x =
      (V.ι ≫ g).fiberToSpecResidueField x := by
  simp only [Scheme.Hom.fiberRestrictIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc]
  change _ ≫ (pullbackSymmetry V.ι (pullback.fst g (X.fromSpecResidueField x))).hom ≫
    pullback.fst (pullback.fst g (X.fromSpecResidueField x)) V.ι ≫
      pullback.snd g (X.fromSpecResidueField x) = pullback.snd (V.ι ≫ g) (X.fromSpecResidueField x)
  rw [pullbackSymmetry_hom_comp_fst_assoc]
  exact pullbackRightPullbackFstIso_inv_snd_snd g (X.fromSpecResidueField x) V.ι

omit [IsAffineHom g] in
/-- The fibre degree of the restriction of `g` to an open `V` is the dimension of the sections
of the fibre of `g` over the corresponding open. -/
lemma Scheme.Hom.fiberDegree_comp_ι (V : U.Opens) [IsAffineHom (V.ι ≫ g)] :
    letI := (((g.fiberι x) ⁻¹ᵁ V).ι ≫ g.fiberToSpecResidueField x).ΓAlgebra
    (V.ι ≫ g).fiberDegree x = Module.finrank (X.residueField x) Γ(((g.fiberι x) ⁻¹ᵁ V), ⊤) :=
  Scheme.Hom.finrankΓ_eq_of_iso _ _ (g.fiberRestrictIso x V) (Iso.refl _) (by
    simpa using g.fiberRestrictIso_hom_ι_fiberToSpecResidueField x V)

include h in
/-- **Additivity of the fibre degree** in complementary open (and closed) subschemes of the
source. -/
lemma Scheme.Hom.fiberDegree_of_isCompl [Module.Finite (X.residueField x) Γ(g.fiber x, ⊤)] :
    haveI := isClosedImmersion_ι_of_isCompl_left h
    haveI := isClosedImmersion_ι_of_isCompl_right h
    g.fiberDegree x = (V₁.ι ≫ g).fiberDegree x + (V₂.ι ≫ g).fiberDegree x := by
  have := isClosedImmersion_ι_of_isCompl_left h
  have := isClosedImmersion_ι_of_isCompl_right h
  rw [g.fiberDegree_comp_ι x V₁, g.fiberDegree_comp_ι x V₂]
  let Z := g.fiber x
  let ι := g.fiberι x
  let hZ := g.fiberToSpecResidueField x
  let O₁ : Z.Opens := ι ⁻¹ᵁ V₁
  let O₂ : Z.Opens := ι ⁻¹ᵁ V₂
  let _ := (O₁.ι ≫ hZ).ΓAlgebra
  let _ := (O₂.ι ≫ hZ).ΓAlgebra
  have hO : IsCompl O₁ O₂ := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      change ι ⁻¹ᵁ V₁ ⊓ ι ⁻¹ᵁ V₂ = ⊥
      rw [← Scheme.Hom.preimage_inf, h.inf_eq_bot]
      rfl
    · rw [codisjoint_iff]
      change ι ⁻¹ᵁ V₁ ⊔ ι ⁻¹ᵁ V₂ = ⊤
      rw [← Scheme.Hom.preimage_sup, h.sup_eq_top]
      rfl
  -- The restriction maps as `κ(x)`-algebra homomorphisms.
  let r₁ : Γ(Z, ⊤) →ₐ[X.residueField x] Γ(O₁, ⊤) :=
    { O₁.ι.appTop.hom with commutes' := fun _ ↦ rfl }
  let r₂ : Γ(Z, ⊤) →ₐ[X.residueField x] Γ(O₂, ⊤) :=
    { O₂.ι.appTop.hom with commutes' := fun _ ↦ rfl }
  have hbij : Function.Bijective (r₁.prod r₂) := by
    have := Z.bijective_restrict_prod_of_isCompl (O₁ := O₁.ι ''ᵁ ⊤) (O₂ := O₂.ι ''ᵁ ⊤) (by
      simpa only [Scheme.Opens.ι_image_top] using hO)
    exact this
  let e : Γ(Z, ⊤) ≃ₐ[X.residueField x] Γ(O₁, ⊤) × Γ(O₂, ⊤) := AlgEquiv.ofBijective _ hbij
  have h₁ : Module.Finite (X.residueField x) Γ(O₁, ⊤) :=
    Module.Finite.of_surjective (LinearMap.fst _ _ _ ∘ₗ e.toLinearEquiv.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have h₂ : Module.Finite (X.residueField x) Γ(O₂, ⊤) :=
    Module.Finite.of_surjective (LinearMap.snd _ _ _ ∘ₗ e.toLinearEquiv.toLinearMap)
      (Prod.snd_surjective.comp e.surjective)
  change Module.finrank _ _ = _
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod]

end IsCompl

section Spec

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (x : PrimeSpectrum R)

/-- The scheme-theoretic fibre degree of `Spec S ⟶ Spec R` at a prime `p` is the ring-theoretic
fibre degree `Ideal.fiberDegree p S`. -/
lemma Scheme.Hom.fiberDegree_SpecMap :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberDegree x = x.asIdeal.fiberDegree S := by
  let a := Spec.fiberToSpecResidueFieldIso R S x
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let i : (Spec (.of R)).residueField x ≅ .of x.asIdeal.ResidueField :=
    Scheme.Spec.residueFieldIso (.of R) x
  have ha : a.hom.right = Spec.map i.inv := rfl
  have he : (Arrow.leftFunc.mapIso a).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S))) ≫
        Spec.map i.hom = g.fiberToSpecResidueField x := by
    have hw := a.hom.w
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, ha] at hw
    change a.hom.left ≫ _ = _
    rw [← Category.assoc, hw, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
      Category.comp_id]
  have h1 := Scheme.Hom.finrankΓ_eq_of_iso (g.fiberToSpecResidueField x)
    (Spec.map (CommRingCat.ofHom (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S))))
    (Arrow.leftFunc.mapIso a) i he
  refine h1.trans ?_
  let _ := (Spec.map (CommRingCat.ofHom
    (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S)))).ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (.of (x.asIdeal.Fiber S))).commRingCatIsoToRingEquiv ?_
  refine RingHom.ext fun y ↦ ?_
  change algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S) y =
    (Scheme.ΓSpecIso (.of (x.asIdeal.Fiber S))).hom
      (((Scheme.ΓSpecIso (.of x.asIdeal.ResidueField)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S)))).appTop) y)
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- For a standard étale algebra the scheme-theoretic fibre degrees are bounded. -/
lemma Scheme.Hom.exists_forall_fiberDegree_SpecMap_le [Algebra.IsStandardEtale R S] :
    ∃ n : ℕ, ∀ x : PrimeSpectrum R,
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberDegree x ≤ n := by
  obtain ⟨n, hn⟩ := Algebra.IsStandardEtale.exists_forall_fiberDegree_le R S
  exact ⟨n, fun x ↦ by rw [Scheme.Hom.fiberDegree_SpecMap]; exact hn x.asIdeal⟩

end Spec

end FiberDegree

section Field

variable {K : Type u} [Field K]

/-- The order `f.finrankΓ` of a finite group scheme over a field is the fibre degree of its
structure morphism at the unique point of `Spec K`; the two degree notions of the project agree
on group schemes over a field. -/
theorem fiberDegree_eq_finrankΓ {G : Scheme.{u}} (f : G ⟶ Spec (.of K)) [IsAffineHom f]
    (x : Spec (.of K)) :
    f.fiberDegree x = f.finrankΓ := by
  have : IsAffine G := isAffine_of_isAffineHom f
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((Spec (.of K)).fromSpecResidueField x)
  have H : IsPullback (pullback.fst f _) (f.fiberToSpecResidueField x) f (Spec.map ψ) := by
    rw [hψ]; exact .of_hasPullback _ _
  obtain ⟨e⟩ := Scheme.Hom.nonempty_algEquiv_tensorProduct_Γ_of_isPullback ψ H
  let _ := f.ΓAlgebra
  let _ := ψ.hom.toAlgebra
  have e' : (Spec (.of K)).residueField x ⊗[K] Γ(G, ⊤) ≃ₐ[(Spec (.of K)).residueField x]
      Γ(f.fiber x, ⊤) := e
  change Module.finrank _ _ = Module.finrank _ _
  rw [← e'.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange


/-- The order of a finite scheme over a field is invariant under extension of the base field:
for an affine `f : G ⟶ Spec K` and a field `L` over `K`, the base change `G_L ⟶ Spec L` has
`dim_L Γ(G_L, 𝒪) = dim_K Γ(G, 𝒪)`. -/
theorem Scheme.Hom.finrankΓ_pullback_snd {G : Scheme.{u}} (f : G ⟶ Spec (.of K)) [IsAffineHom f]
    {L : Type u} [Field L] (g : Spec (.of L) ⟶ Spec (.of K)) :
    (pullback.snd f g).finrankΓ = f.finrankΓ := by
  obtain ⟨x⟩ : Nonempty (Spec (.of L)) := inferInstance
  rw [← fiberDegree_eq_finrankΓ _ x, Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback f g),
    fiberDegree_eq_finrankΓ]

end Field

section GenericPoint

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]

/-- Every point of the fibre of a locally quasi-finite morphism `f` from an integral scheme
through the generic point `η` of the source is `η`. -/
lemma Scheme.Hom.eq_asFiber_genericPoint [LocallyQuasiFinite f]
    (p : f.fiber (f (genericPoint X))) :
    p = f.asFiber (genericPoint X) := by
  have h : f.fiberι _ (f.asFiber (genericPoint X)) ⤳ f.fiberι _ p := by
    rw [f.fiberι_asFiber]; exact genericPoint_specializes _
  exact (specializes_iff_eq.mp
    ((f.fiberι _).isEmbedding.toIsInducing.specializes_iff.mp h)).symm

/-- The local rings of the fibre of a locally quasi-finite morphism `f` from an integral scheme
through the generic point of the source are fields: they are quotients of the function field. -/
lemma Scheme.Hom.isField_stalk_fiber_genericPoint [LocallyQuasiFinite f]
    (p : f.fiber (f (genericPoint X))) :
    IsField ((f.fiber (f (genericPoint X))).presheaf.stalk p) := by
  have hp : f.fiberι _ p = genericPoint X := by
    rw [f.eq_asFiber_genericPoint p, f.fiberι_asFiber]
  have hK : IsField (X.presheaf.stalk (f.fiberι _ p)) := by
    rw [hp]; exact Field.toIsField X.functionField
  let := hK.toField
  exact MulEquiv.isField hK (RingEquiv.ofBijective ((f.fiberι _).stalkMap p).hom
    ⟨((f.fiberι _).stalkMap p).hom.injective, (f.fiberι _).stalkMap_surjective p⟩).symm

/-- The fibre of a locally quasi-finite morphism `f` from an integral scheme through the generic
point `η` of the source is `Spec κ(η)`. -/
instance Scheme.Hom.isIso_asFiberHom_genericPoint [LocallyQuasiFinite f] :
    IsIso (f.asFiberHom (genericPoint X)) := by
  let z : Spec (X.residueField (genericPoint X)) := IsLocalRing.closedPoint _
  have hsurj : Function.Surjective (f.asFiberHom (genericPoint X)) := fun p ↦
    ⟨z, (f.asFiberHom_apply _ z).trans (f.eq_asFiber_genericPoint p).symm⟩
  have : ∀ x, IsIso ((f.asFiberHom (genericPoint X)).stalkMap x) := fun x ↦ by
    let := (f.isField_stalk_fiber_genericPoint (f.asFiberHom _ x)).toField
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨((f.asFiberHom _).stalkMap x).hom.injective, (f.asFiberHom _).stalkMap_surjective x⟩
  have : IsOpenImmersion (f.asFiberHom (genericPoint X)) :=
    .of_isIso_stalkMap _ ⟨(f.asFiberHom _).isEmbedding, by
      rw [hsurj.range_eq]; exact isOpen_univ⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨this, ⟨hsurj⟩⟩

/-- The degree of the fibre of a quasi-finite affine morphism `f` from an integral scheme through
the generic point `η` of the source is the degree `[κ(η) : κ(f η)]` of the residue field
extension. -/
theorem Scheme.Hom.fiberDegree_genericPoint [IsAffineHom f] [LocallyQuasiFinite f] :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    f.fiberDegree (f (genericPoint X)) =
      Module.finrank (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) := by
  have := Scheme.Hom.finrankΓ_eq_of_iso (Spec.map (f.residueFieldMap (genericPoint X)))
    (f.fiberToSpecResidueField _) (asIso (f.asFiberHom (genericPoint X))) (Iso.refl _) (by simp)
  let _ := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have h := Scheme.Hom.finrankΓ_SpecMap (Y.residueField (f (genericPoint X)))
    (X.residueField (genericPoint X))
  exact this.symm.trans h

omit [IsIntegral X] in
/-- A dominant morphism of irreducible schemes maps the generic point to the generic point. -/
lemma Scheme.Hom.apply_genericPoint_of_isDominant [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at this

/-- If a finite morphism `f: X ⟶ Y` from an integral scheme has all fibres of degree `n`, then
the degree `[κ(η): κ(f η)]` of the residue field extension at the generic point `η` of `X` is
`n`; for `f` dominant and `Y` integral this is the degree `[k(X): k(Y)]` of the
extension of function fields. -/
theorem Scheme.Hom.finrank_residueField_genericPoint_of_fiberDegree_eq [IsFinite f] {n : ℕ}
    (h : ∀ y, f.fiberDegree y = n) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    Module.finrank (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) = n :=
  f.fiberDegree_genericPoint.symm.trans (h _)

end GenericPoint

section FlatOfFiberDegree

variable {X Y : Scheme.{u}}

/-- The fibre degree is invariant under precomposition with an isomorphism. -/
lemma Scheme.Hom.fiberDegree_comp_left_of_isIso {X' : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (f : X ⟶ Y) [IsAffineHom f] (y : Y) :
    (e ≫ f).fiberDegree y = f.fiberDegree y :=
  Scheme.Hom.fiberDegree_of_isPullback f
    (IsPullback.of_horiz_isIso (fst := e) (snd := e ≫ f) (g := 𝟙 Y) ⟨by simp⟩) y

set_option backward.isDefEq.respectTransparency false in
/-- The affine case of `AlgebraicGeometry.Scheme.Hom.flat_of_fiberDegree_eq` and
`AlgebraicGeometry.Scheme.Hom.finrank_eq_of_fiberDegree_eq`, which reduces to
`Module.projective_of_finrank_fiber_eq`. -/
private lemma Scheme.Hom.flat_and_finrank_of_fiberDegree_eq_of_affine {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsAffine X] [IsFinite f] [LocallyOfFinitePresentation f] [_root_.IsReduced R]
    {n : ℕ} (h : ∀ y, f.fiberDegree y = n) : Flat f ∧ ∀ y, f.finrank y = n := by
  wlog hX : ∃ S, X = Spec S generalizing X
  · obtain ⟨h₁, h₂⟩ := this (X.isoSpec.inv ≫ f)
      (fun y ↦ (Scheme.Hom.fiberDegree_comp_left_of_isIso _ _ _).trans (h y)) ⟨_, rfl⟩
    refine ⟨?_, fun y ↦ ?_⟩
    · rwa [MorphismProperty.cancel_left_of_respectsIso @Flat] at h₁
    · have := (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp h₁
      rw [← h₂ y, Scheme.Hom.finrank_comp_left_of_isIso]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  algebraize [φ.hom]
  have : Module.FinitePresentation R S :=
    .of_finite_of_finitePresentation _ _
  have h' (q : Ideal R) [q.IsPrime] :
      Module.finrank q.ResidueField (q.Fiber S) = n := by
    have e : φ = CommRingCat.ofHom (algebraMap R S) := rfl
    rw [← h ⟨q, inferInstance⟩, e, Scheme.Hom.fiberDegree_SpecMap]
    rfl
  have := Module.projective_of_finrank_fiber_eq h'
  have hflat : φ.hom.Flat := by
    rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.flat_algebraMap_iff]; infer_instance
  refine ⟨Flat.SpecMap_iff.mpr hflat, fun y ↦ ?_⟩
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank ‹_› hflat, ← RingHom.algebraMap_toAlgebra φ.hom,
    RingHom.finrank_algebraMap]
  exact Module.rankAtStalk_eq_of_finrank_fiber_eq h' y

variable (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] [IsReduced Y] {n : ℕ}

/-- A finite morphism `f: X ⟶ Y` of finite presentation to a reduced scheme, all of whose fibres
have the same degree `n`, is flat. -/
theorem Scheme.Hom.flat_of_fiberDegree_eq (h : ∀ y, f.fiberDegree y = n) : Flat f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) Y.affineCover]
  intro i
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have := (affine_isReduced_iff _).mp this
  have : IsAffine (pullback f (Y.affineCover.f i)) :=
    isAffine_of_isAffineHom (pullback.snd f (Y.affineCover.f i))
  exact (flat_and_finrank_of_fiberDegree_eq_of_affine (pullback.snd f (Y.affineCover.f i))
    fun y ↦ (Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback _ _) y).trans (h _)).1

/-- A finite morphism `f: X ⟶ Y` of finite presentation to a reduced scheme, all of whose fibres
have the same degree `n`, is finite flat of rank `n`: `f_* 𝒪_X` is locally free of rank `n`. -/
theorem Scheme.Hom.finrank_eq_of_fiberDegree_eq (h : ∀ y, f.fiberDegree y = n) (y : Y) :
    f.finrank y = n := by
  have := f.flat_of_fiberDegree_eq h
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.finrank_pullback_snd]
  have : IsReduced (Spec R) := isReduced_of_isOpenImmersion g
  have : _root_.IsReduced R := (affine_isReduced_iff _).mp this
  have : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  exact (flat_and_finrank_of_fiberDegree_eq_of_affine (pullback.snd f g)
    fun y ↦ (Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback _ _) y).trans (h _)).2 y

end FlatOfFiberDegree

section ClosedPoints

variable {X Y : Scheme.{u}}

/-- The affine case of `AlgebraicGeometry.Scheme.Hom.eventually_fiberDegree_le`, which reduces
to `Module.exists_finrank_fiber_le`. -/
private lemma Scheme.Hom.exists_fiberDegree_le_of_affine {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    [IsAffine X] [IsFinite f] (y : Spec R) :
    ∃ a ∉ y.asIdeal, ∀ z : Spec R, a ∉ z.asIdeal → f.fiberDegree z ≤ f.fiberDegree y := by
  wlog hX : ∃ S, X = Spec S generalizing X
  · obtain ⟨a, hay, ha⟩ := this (X.isoSpec.inv ≫ f) ⟨_, rfl⟩
    refine ⟨a, hay, fun z hz ↦ ?_⟩
    simpa only [Scheme.Hom.fiberDegree_comp_left_of_isIso] using ha z hz
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff] at *
  algebraize [φ.hom]
  have e : φ = CommRingCat.ofHom (algebraMap R S) := rfl
  obtain ⟨a, hay, ha⟩ := Module.exists_finrank_fiber_le (R := R) (M := S) y.asIdeal
  refine ⟨a, hay, fun z hz ↦ ?_⟩
  rw [e, Scheme.Hom.fiberDegree_SpecMap, Scheme.Hom.fiberDegree_SpecMap]
  exact ha z.asIdeal hz

variable (f : X ⟶ Y) [IsFinite f]

/-- **Upper semicontinuity of the fibre degree.** The fibre degree of a finite morphism `f` does
not increase near a point: `f.fiberDegree y' ≤ f.fiberDegree y` for all `y'` near `y`. -/
theorem Scheme.Hom.eventually_fiberDegree_le (y : Y) :
    ∀ᶠ y' in 𝓝 y, f.fiberDegree y' ≤ f.fiberDegree y := by
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  obtain ⟨a, hay, ha⟩ := (pullback.snd f g).exists_fiberDegree_le_of_affine y
  have hD : IsOpen (X := Spec R) {z | a ∉ z.asIdeal} := (PrimeSpectrum.basicOpen a).isOpen
  refine Filter.mem_of_superset ((g.isOpenEmbedding.isOpenMap _ hD).mem_nhds ⟨y, hay, rfl⟩) ?_
  rintro _ ⟨z, hz, rfl⟩
  change f.fiberDegree (g z) ≤ f.fiberDegree (g y)
  rw [← Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback _ _) z,
    ← Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback _ _) y]
  exact ha z hz

variable [JacobsonSpace Y] {n : ℕ}

/-- Let `f` be a finite morphism to a Jacobson scheme (for example a scheme locally of finite
type over a field). If the fibres of `f` over all closed points have degree `n`, then all fibres
of `f` have degree `n`. -/
theorem Scheme.Hom.fiberDegree_eq_of_forall_isClosed
    (h : ∀ y : Y, IsClosed {y} → f.fiberDegree y = n) (y : Y) : f.fiberDegree y = n := by
  apply le_antisymm
  · obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure {y})
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    rw [← h z hzc]
    exact ((f.eventually_fiberDegree_le z).filter_mono
      (specializes_iff_mem_closure.mpr hz)).self_of_nhds
  · obtain ⟨U, hUy, hU, hyU⟩ := mem_nhds_iff.mp (f.eventually_fiberDegree_le y)
    obtain ⟨z, ⟨hzU, -⟩, hzc⟩ := nonempty_inter_closedPoints (Z := U ∩ closure {y})
      ⟨y, hyU, subset_closure rfl⟩ (hU.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
    rw [← h z hzc]
    exact hUy hzU

variable [LocallyOfFinitePresentation f] [IsReduced Y]

/-- A finite morphism `f: X ⟶ Y` of finite presentation to a reduced Jacobson scheme (for example
a reduced scheme of finite type over a field), whose fibres over all closed points of `Y` have
the same degree `n`, is flat. -/
theorem Scheme.Hom.flat_of_fiberDegree_eq_of_isClosed
    (h : ∀ y : Y, IsClosed {y} → f.fiberDegree y = n) : Flat f :=
  f.flat_of_fiberDegree_eq (f.fiberDegree_eq_of_forall_isClosed h)

/-- A finite morphism `f: X ⟶ Y` of finite presentation to a reduced Jacobson scheme, whose fibres
over all closed points of `Y` have the same degree `n`, is finite flat of rank `n`: `f_* 𝒪_X` is
locally free of rank `n`. -/
theorem Scheme.Hom.finrank_eq_of_fiberDegree_eq_of_isClosed
    (h : ∀ y : Y, IsClosed {y} → f.fiberDegree y = n) (y : Y) : f.finrank y = n :=
  f.finrank_eq_of_fiberDegree_eq (f.fiberDegree_eq_of_forall_isClosed h) y

omit [LocallyOfFinitePresentation f] [IsReduced Y] in
/-- If a finite morphism `f: X ⟶ Y` from an integral scheme to a Jacobson scheme has all fibres
over closed points of degree `n`, then the degree `[κ(η): κ(f η)]` of the residue field
extension at the generic point `η` of `X` is `n`; for `f` dominant and `Y` integral this is the
degree `[k(X): k(Y)]` of the extension of function fields. -/
theorem Scheme.Hom.finrank_residueField_genericPoint_of_fiberDegree_eq_of_isClosed
    [IsIntegral X] (h : ∀ y : Y, IsClosed {y} → f.fiberDegree y = n) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    Module.finrank (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) = n :=
  f.finrank_residueField_genericPoint_of_fiberDegree_eq (f.fiberDegree_eq_of_forall_isClosed h)

end ClosedPoints

section FiniteLocallyFree

variable {X S : Scheme.{u}}

/-- A morphism of schemes `f: X ⟶ S` is **finite locally free** if it is finite, flat and
locally of finite presentation. -/
class Scheme.Hom.IsFiniteLocallyFree (f : X ⟶ S) : Prop
    extends IsFinite f, Flat f, LocallyOfFinitePresentation f

/-- A morphism of schemes `f: X ⟶ S` is **finite locally free of degree `d`** if it is finite
locally free and every fibre `X_s` has degree `d`: `dim_{κ(s)} Γ(X_s, 𝒪_{X_s}) = d` for every point
`s` of `S` (`AlgebraicGeometry.Scheme.Hom.fiberDegree`). -/
class Scheme.Hom.IsFiniteLocallyFreeOfDegree (f : X ⟶ S) (d : ℕ) : Prop
    extends f.IsFiniteLocallyFree where
  fiberDegree_eq (s : S) : f.fiberDegree s = d

end FiniteLocallyFree

end AlgebraicGeometry
