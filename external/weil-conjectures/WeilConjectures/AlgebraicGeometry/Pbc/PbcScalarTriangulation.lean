/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Canonical rational triangulation adapters

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## Implementation details

The `Fact`-based adapters expose the same selected witness as `pbcRationalTriangulationData`,
with its shift and image-triangle normalizations. They allow instance synthesis when the raw
category abbreviation erases the geometric proofs.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace CategoryTheory.ScalarLocalization
open scoped TensorProduct
private noncomputable def pbcRationalComparison
    (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem pbcScalarLocalization_isLocalization
    (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (localization R C p).IsLocalization (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := pbcRationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, localization, pbcRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

end CategoryTheory.ScalarLocalization

namespace AlgebraicGeometry.Scheme
section Triangulation
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Expose the rational-transport triangulation `pbcRationalTriangulationData` through `Fact`
hypotheses. -/
@[instance] theorem pbcScalarRationalZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    HasZeroObject (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) := by
  exact (pbcRationalTriangulationData l E T Fact.out Fact.out).choose

/-- Expose the rational-transport triangulation `pbcRationalTriangulationData` through `Fact`
hypotheses. -/
instance pbcScalarRationalHasShift : HasShift (PbcRationalCategory T (pbcIntegralDatum l E)
  (pbcUniformizer l E)) ℤ :=
  (pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose

/-- Expose the rational-transport triangulation `pbcRationalTriangulationData` through `Fact`
hypotheses. -/
@[instance] theorem pbcScalarRationalShiftAdditive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∀ n : ℤ, (shiftFunctor (PbcRationalCategory T (pbcIntegralDatum l E)
      (pbcUniformizer l E)) n).Additive := by
  exact (pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2.choose

/-- Expose the rational-transport triangulation `pbcRationalTriangulationData` through `Fact`
hypotheses. -/
instance pbcScalarRationalLocalizationShift : (ScalarLocalization.localization
  (PbcIntegralRing l E) (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (pbcUniformizer l E)).CommShift ℤ :=
  ((pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose

/-- Expose the rational-transport triangulation `pbcRationalTriangulationData` through `Fact`
hypotheses. -/
instance pbcScalarRationalPretriangulated : Pretriangulated (PbcRationalCategory T
  (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  ((pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose_spec.2.choose

/-- Expose the existing isomorphism closure of the integral predicate. -/
instance pbcScalarIntegralIsoClosure :
    ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) :=
  (pbcIntegralUniformComplete_isTriangulated l E T Fact.out Fact.out).1

/-- Expose the existing canonical field action through the geometric Fact hypotheses. -/
instance pbcScalarRationalLinear :
    Linear E (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  pbcRationalLinear l E T Fact.out Fact.out

end Triangulation
end AlgebraicGeometry.Scheme
