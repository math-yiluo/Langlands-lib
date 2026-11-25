/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Finite Galois field extensions are Galois covers

Let `L/F` be a finite Galois extension of fields and `g : Spec L ⟶ Spec F` the induced morphism.
The Galois group `Gal(L/F)` acts on `Spec L` over `Spec F` through `σ ↦ Spec σ`
(`AlgebraicGeometry.specGaloisAction`), and this action is *Galois* in the sense of
`AlgebraicGeometry.ProEtale.IsGaloisAction` (`AlgebraicGeometry.ProEtale.isGaloisAction_spec`):
two morphisms `a b : T ⟶ Spec L` agreeing over `Spec F` agree, on the members of an open cover
of `T`, up to an element of the Galois group. Moreover `g` is finite, étale and surjective.

The algebraic input (`AlgebraicGeometry.IsGalois.exists_sum_eq_one_mul_eq`) is the splitting
`L ⊗_F L ≅ ∏_σ L` in a form valid for an arbitrary commutative target ring: for two ring maps
`α β : L → R` agreeing on `F` there are elements `e σ ∈ R` with `∑ σ, e σ = 1` and
`e σ * β y = e σ * α (σ y)`. They are obtained by evaluating the Lagrange interpolation basis at
the conjugates of a primitive element. The open cover is then given by the basic opens `D(e σ)`.

Galois actions are stable under base change (`AlgebraicGeometry.ProEtale.IsGaloisAction.pullback`
for the action `AlgebraicGeometry.ProEtale.pullbackAction` on `X' ×_X Y`); finiteness, étaleness
and surjectivity of `pullback.fst` are inferred from Mathlib's base change instances.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

/-- For a finite Galois extension `L/F` and ring maps `α β : L →+* R` agreeing on `F`, there are
elements `e σ ∈ R`, indexed by the Galois group, with `∑ σ, e σ = 1` and
`e σ * β y = e σ * α (σ y)` for all `y`. This expresses that `L ⊗_F L` is the product of copies
of `L` indexed by `Gal(L/F)`. -/
theorem IsGalois.exists_sum_eq_one_mul_eq {F L R : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] [CommRing R] (α β : L →+* R)
    (h : α.comp (algebraMap F L) = β.comp (algebraMap F L)) :
    ∃ e : (L ≃ₐ[F] L) → R, ∑ σ, e σ = 1 ∧ ∀ σ y, e σ * β y = e σ * α (σ y) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F L
  let v : (L ≃ₐ[F] L) → L := fun σ ↦ σ pb.gen
  have hv : Function.Injective v := fun σ τ hστ ↦
    AlgEquiv.coe_toAlgHom_injective (pb.algHom_ext (f := σ.toAlgHom) (g := τ.toAlgHom) hστ)
  have hq : (minpoly F pb.gen).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  -- The minimal polynomial of the primitive element is the product over its conjugates.
  have hnodal : (minpoly F pb.gen).map (algebraMap F L) = Lagrange.nodal Finset.univ v := by
    refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic (hq.map _) ?_ ?_
    · refine dvd_trans (dvd_of_eq ?_)
        ((Multiset.prod_X_sub_C_dvd_iff_le_roots (hq.map _).ne_zero (Finset.univ.val.map v)).2 ?_)
      · rw [Multiset.map_map]
        rfl
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map hv)]
      rintro _ hx
      obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.1 hx
      rw [mem_roots (hq.map _).ne_zero, IsRoot, eval_map_algebraMap, aeval_algHom_apply,
        minpoly.aeval, map_zero]
    · rw [natDegree_map, pb.natDegree_minpoly, ← pb.finrank, Lagrange.natDegree_nodal,
        Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let e : (L ≃ₐ[F] L) → R := fun σ ↦ eval₂RingHom α (β pb.gen) (Lagrange.basis Finset.univ v σ)
  refine ⟨e, ?_, fun σ y ↦ ?_⟩
  · rw [← map_sum, Lagrange.sum_basis hv.injOn Finset.univ_nonempty, map_one]
  have hσ : (β pb.gen - α (σ pb.gen)) * e σ = 0 := by
    have hX : (X - C (v σ)) * Lagrange.basis Finset.univ v σ =
        C (Lagrange.nodalWeight Finset.univ v σ) * Lagrange.nodal Finset.univ v := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ σ),
        ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ σ), mul_left_comm,
        ← Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ σ)]
    have := congrArg (eval₂RingHom α (β pb.gen)) hX
    rw [← hnodal, map_mul, map_mul] at this
    simp only [coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C, eval₂_map, h, ← hom_eval₂,
      ← aeval_def, minpoly.aeval, map_zero, mul_zero] at this
    exact this
  obtain ⟨p, -, rfl⟩ := pb.exists_eq_aeval y
  obtain ⟨k, hk⟩ := sub_dvd_eval_sub (β pb.gen) (α (σ pb.gen)) (p.map (β.comp (algebraMap F L)))
  rw [← sub_eq_zero, ← mul_sub, ← aeval_algHom_apply σ, aeval_def, aeval_def, hom_eval₂,
    hom_eval₂, h, ← Polynomial.eval_map, ← Polynomial.eval_map, hk, mul_left_comm, ← mul_assoc,
    hσ, zero_mul]

variable (F L : Type u) [Field F] [Field L] [Algebra F L]

/-- The action `Spec σ : Spec L ⟶ Spec L` of an `F`-automorphism `σ` of `L`. -/
noncomputable def specGaloisAction (σ : L ≃ₐ[F] L) : Spec (.of L) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (σ : L →+* L))

/-- `Spec L ⟶ Spec F` is finite for a finite field extension `L/F` (instance form; the former
lemma `AlgebraicGeometry.isFinite_specMap_algebraMap` of `Picard/Jacobian.lean` was a duplicate
of it). -/
instance instIsFiniteSpecMapAlgebraMap [FiniteDimensional F L] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F L))) :=
  (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)

/-- `Spec L ⟶ Spec F` is étale for a finite separable field extension `L/F`. -/
instance etale_specMap_algebraMap [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap F L))) :=
  HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 .of_finite_of_isSeparable)

/-- `Spec L ⟶ Spec F` is surjective for a field extension `L/F`: `Spec F` is a point (the instance
form of `AlgebraicGeometry.surjective_specMap_algebraMap`). -/
instance instSurjectiveSpecMapAlgebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap F L))) :=
  ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

variable {F L}

/-- The Galois action on `Spec L` is an action over `Spec F`. -/
@[reassoc (attr := simp)]
lemma specGaloisAction_comp (σ : L ≃ₐ[F] L) :
    specGaloisAction F L σ ≫ Spec.map (CommRingCat.ofHom (algebraMap F L)) =
      Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
  rw [specGaloisAction, ← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- `σ ↦ Spec σ` is compatible with multiplication: `Spec σ ≫ Spec τ = Spec (σ * τ)`. -/
lemma specGaloisAction_mul (σ τ : L ≃ₐ[F] L) :
    specGaloisAction F L σ ≫ specGaloisAction F L τ = specGaloisAction F L (σ * τ) := by
  rw [specGaloisAction, specGaloisAction, specGaloisAction, ← Spec.map_comp]
  rfl

/-- The ring map `L →+* Γ(T, ⊤)` corresponding to a morphism `T ⟶ Spec L`. -/
private noncomputable abbrev specHomRingHom {T : Scheme.{u}} (a : T ⟶ Spec (.of L)) :
    L →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of L)).inv ≫ a.appTop).hom

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- The action of `Gal(L/F)` on `Spec L` over `Spec F` is Galois: two morphisms `T ⟶ Spec L`
agreeing over `Spec F` agree, on the basic opens of an open cover of `T`, up to the action of an
element of the Galois group. -/
theorem isGaloisAction_spec :
    IsGaloisAction (Spec.map (CommRingCat.ofHom (algebraMap F L))) (specGaloisAction F L) := by
  intro T a b hab
  have h : (specHomRingHom a).comp (algebraMap F L) = (specHomRingHom b).comp (algebraMap F L) := by
    have := congrArg Scheme.Hom.appTop hab
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at this
    have := congrArg (fun φ ↦ (Scheme.ΓSpecIso (.of F)).inv ≫ φ) this
    simp only [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality] at this
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨e, he1, he⟩ := IsGalois.exists_sum_eq_one_mul_eq _ _ h
  refine ⟨fun σ ↦ T.basicOpen (e σ), fun x ↦ ?_, fun σ ↦ ?_⟩
  · have hspan : Ideal.span (Set.range e) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← he1]
      exact Ideal.sum_mem _ fun σ _ ↦ Ideal.subset_span ⟨σ, rfl⟩
    have hx : x ∈ (⊤ : T.Opens) := trivial
    rw [← iSup_basicOpen_of_span_eq_top _ _ hspan] at hx
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  · refine ext_of_isAffine ?_
    have hunit : IsUnit ((T.basicOpen (e σ)).ι.appTop (e σ)) := by
      refine RingedSpace.isUnit_of_isUnit_germ (T.basicOpen (e σ)).toScheme.toRingedSpace ⊤ _
        fun x _ ↦ ?_
      rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
      exact x.2
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      ← cancel_epi (Scheme.ΓSpecIso (.of L)).inv, specGaloisAction]
    simp only [← Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext y
    refine hunit.mul_left_cancel ?_
    have := congrArg (T.basicOpen (e σ)).ι.appTop (he σ y)
    simp only [map_mul, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this

section BaseChange

variable {X Y X' : Scheme.{u}} (f : X' ⟶ X) (g : Y ⟶ X) {Γ : Type u} {ρ : Γ → (Y ⟶ Y)}
  (hρ : ∀ i, ρ i ≫ g = g)

/-- The action of `ρ` on the base change `X' ×_X Y ⟶ X'` of `g`, through the second factor. -/
noncomputable def pullbackAction (i : Γ) : pullback f g ⟶ pullback f g :=
  pullback.map f g f g (𝟙 _) (ρ i) (𝟙 _) (by simp) (by simp [hρ])

/-- The base changed action is an action over `X'`. -/
@[reassoc (attr := simp)]
lemma pullbackAction_fst (i : Γ) :
    pullbackAction f g hρ i ≫ pullback.fst f g = pullback.fst f g := by
  simp [pullbackAction]

/-- The base changed action acts through `ρ` on the second factor. -/
@[reassoc (attr := simp)]
lemma pullbackAction_snd (i : Γ) :
    pullbackAction f g hρ i ≫ pullback.snd f g = pullback.snd f g ≫ ρ i := by
  simp [pullbackAction]

/-- The base change of an action is an action. -/
lemma pullbackAction_mul [Mul Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (a b : Γ) :
    pullbackAction f g hρ a ≫ pullbackAction f g hρ b = pullbackAction f g hρ (a * b) := by
  ext <;> simp [← hmul]

/-- Galois actions are stable under base change: the action of `ρ` on `X' ×_X Y` over `X'` is
again Galois. -/
theorem IsGaloisAction.pullback [WeaklyEtale g] (hgal : IsGaloisAction g ρ) :
    IsGaloisAction (pullback.fst f g) (pullbackAction f g hρ) := by
  intro T a b hab
  obtain ⟨U, hU, hUρ⟩ := hgal T (a ≫ pullback.snd f g) (b ≫ pullback.snd f g) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hab])
  refine ⟨U, hU, fun i ↦ ?_⟩
  ext
  · simp [hab]
  · simpa using hUρ i


end BaseChange

end AlgebraicGeometry.ProEtale
