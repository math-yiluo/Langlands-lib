/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.LocalizedSeparablePolynomialModel
import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.AdjoinRootCoverFiniteEtale
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Spreading a finite separable extension

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`
(blueprint: lem-weil-pbc-spread-finite-separable-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry

private theorem polynomial_model_equiv_adjoin
    {R : Type*} [CommRing R] {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] [Algebra R L] [FaithfulSMul R L]
    (φ : R →+* K) (hφ : (algebraMap K L).comp φ = algebraMap R L)
    (α : L) (f : Polynomial R) (hf : f.Monic) (hmin : f.map φ = minpoly K α) :
    Nonempty (AdjoinRoot f ≃ₐ[R] Algebra.adjoin R ({α} : Set L)) := by
  have hinj : Function.Injective φ := by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R L
    rw [← hφ]
    exact congrArg (algebraMap K L) h
  have heval (q : Polynomial R) :
      Polynomial.aeval α (q.map φ) = Polynomial.aeval α q := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map, hφ]
  have hroot : Polynomial.aeval α f = 0 := by
    rw [← heval, hmin]
    exact minpoly.aeval K α
  let B := Algebra.adjoin R ({α} : Set L)
  let β : B := ⟨α, Algebra.subset_adjoin (Set.mem_singleton α)⟩
  have hrootB : Polynomial.aeval β f = 0 := by
    apply Subtype.val_injective
    change B.val (Polynomial.aeval β f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hroot
  let ψ : AdjoinRoot f →ₐ[R] B :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R B) β hrootB
  have hψ (q : Polynomial R) : (ψ (AdjoinRoot.mk f q) : L) =
      Polynomial.aeval α q := by
    change B.val (ψ (AdjoinRoot.mk f q)) = _
    rw [AdjoinRoot.liftAlgHom_mk]
    change B.val (Polynomial.aeval β q) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  refine ⟨AlgEquiv.ofBijective ψ ⟨?_, ?_⟩⟩
  · apply (injective_iff_map_eq_zero ψ).mpr
    intro z hz
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (Polynomial.map_dvd_map φ hinj hf).mp
    rw [hmin]
    apply minpoly.dvd K α
    rw [heval, ← hψ, hz]
    rfl
  · intro z
    have hz : (z : L) ∈ (Polynomial.aeval α : Polynomial R →ₐ[R] L).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact z.property
    obtain ⟨q, hq⟩ := hz
    refine ⟨AdjoinRoot.mk f q, ?_⟩
    apply Subtype.val_injective
    rw [hψ]
    exact hq

private theorem etale_adjoinRoot_of_isCoprime
    {R : Type u} [CommRing R] (f : Polynomial R) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hcop
  refine Algebra.etale_adjoinRoot_of_isUnit_derivative hf (IsUnit.of_mul_eq_one_right
    (AdjoinRoot.mk f b) ?_)
  simpa [mul_comm] using congrArg (AdjoinRoot.mk f) hab

private theorem fractionRing_adjoin_of_primitive
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (S : Subalgebra A L) (α : L)
    (hgen : IntermediateField.adjoin K ({α} : Set L) = ⊤) :
    IsFractionRing (Algebra.adjoin S ({α} : Set L)) L := by
  let B := Algebra.adjoin S ({α} : Set L)
  let φ : FractionRing B →+* L :=
    IsFractionRing.lift (g := B.val.toRingHom) Subtype.val_injective
  have hA (a : A) : algebraMap A L a ∈ φ.fieldRange := by
    let b : B := algebraMap S B (algebraMap A S a)
    refine ⟨algebraMap B (FractionRing B) b, ?_⟩
    change φ (algebraMap B (FractionRing B) b) = algebraMap A L a
    rw [IsFractionRing.lift_algebraMap]
    change algebraMap S L (algebraMap A S a) = algebraMap A L a
    exact (IsScalarTower.algebraMap_apply A S L a).symm
  have hK (k : K) : algebraMap K L k ∈ φ.fieldRange := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A k
    simpa [map_div₀, ← IsScalarTower.algebraMap_apply A K L] using
      φ.fieldRange.div_mem (hA a) (hA b)
  let F : IntermediateField K L :=
    { φ.fieldRange with algebraMap_mem' := hK }
  have hα : α ∈ F := by
    refine ⟨algebraMap B (FractionRing B)
      ⟨α, Algebra.subset_adjoin (Set.mem_singleton α)⟩, ?_⟩
    change φ (algebraMap B (FractionRing B) _) = α
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have htop : F = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα)
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ F := by rw [htop]; trivial
  obtain ⟨q, hq⟩ := hz
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B q
  refine ⟨a, b, ?_⟩
  rw [← hq, ← hab, map_div₀]
  rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  rfl

/-- A finite separable extension of the fraction field of a Noetherian domain spreads to
 a finite etale domain over a principal localization, with the given extension as fraction
 field. Both rings are represented inside the extension field, with their induced algebra
 structures; `IsLocalization.Away c S` identifies `S` with `A[c⁻¹]`. That `B` is a domain
 is automatic (`B` is a subring of the field `L`), so it is not a separate conjunct.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`
(blueprint: lem-weil-pbc-spread-finite-separable-extension).

Proof:
1. Choose a primitive element alpha by `lem-weil-pbc-finite-separable-primitive-element`.
Its monic minimal polynomial f is irreducible and separable, and
`lem-weil-pbc-minimal-polynomial-quotient-field-iso` identifies K[T]/(f) with K'.
2. Clear the coefficients' denominators and invert the nonzero discriminant, giving a
nonzero c and S = A[c⁻¹]. Then f is monic over S and f' is a unit modulo f. The algebra
B = S[T]/(f) is finite free, embeds in K' via T mapping to alpha, and has fraction field K'.
3. Since f' is invertible modulo f, `lem-weil-pbc-standard-etale-monic-derivative` makes
B etale over S. Its finite free presentation gives finiteness. The inclusion S into B is
injective and integral; `pqf-lem-lying-over` gives surjectivity on spectra.
-/
theorem exists_spread_finite_separable_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ c : A, c ≠ 0 ∧ ∃ S : Subalgebra A L,
      IsLocalization.Away c S ∧ ∃ B : Subalgebra S L,
        Module.Finite S B ∧ Algebra.Etale S B ∧ IsFractionRing B L ∧
        IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S B))) ∧
        Etale (Spec.map (CommRingCat.ofHom (algebraMap S B))) ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap S B))) := by
  obtain ⟨α, hgen⟩ := Field.exists_primitive_element K L
  obtain ⟨c, hc, S, hS, φ, hφ, f, hf, hcop, hmin⟩ :=
    exists_localized_separable_polynomial_model A K L α
      (Algebra.IsIntegral.isIntegral α) (Algebra.IsSeparable.isSeparable K α)
  obtain ⟨e⟩ := polynomial_model_equiv_adjoin φ hφ α f hf hmin
  let B := Algebra.adjoin S ({α} : Set L)
  have hfin : Module.Finite S B := by
    have := hf.finite_adjoinRoot
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  have het : Algebra.Etale S B := by
    have := etale_adjoinRoot_of_isCoprime f hf hcop
    exact Algebra.Etale.of_equiv e
  have hfrac : IsFractionRing B L := fractionRing_adjoin_of_primitive A K L S α hgen
  have hinj : Function.Injective (algebraMap S B) :=
    FaithfulSMul.algebraMap_injective S B
  have hint : (algebraMap S B).IsIntegral := by
    let := hfin
    exact algebraMap_isIntegral_iff.mpr inferInstance
  refine ⟨c, hc, S, hS, B, hfin, het, hfrac, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr het)
  · exact ⟨hint.comap_surjective hinj⟩

end AlgebraicGeometry
