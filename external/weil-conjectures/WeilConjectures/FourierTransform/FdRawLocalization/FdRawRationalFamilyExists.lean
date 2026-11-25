/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData

/-! # The supplied rational stage family in the named presentation

Source: the presentation clause of raw localization scalar-descent step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

open scoped TensorProduct

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

attribute [local irreducible] HasDerivedCategory.standard
  FdOrdinaryScalarTransport.complex FdOrdinaryScalarTransport.completion
  fdCoefficientTransportFactors pbcIntegralDatum completedAdicChangeData
  integralDetailedCoefficientComparison sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.transition
  pbcScalarCommShift pbcRationalHasShift
  ScalarLocalization.composition ScalarLocalization.category

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra

private theorem copyShiftedFunctor
    {C D : Type*} (c c' : Category C) [Category D]
    (s : @HasShift C ℤ c _) (s' : @HasShift C ℤ c' _) [HasShift D ℤ]
    (hc : c = c') (hs : HEq s s')
    (F : @Functor C c D _) (t : @Functor.CommShift C D c _ F ℤ _ s _) :
    ∃ (G : @Functor C c' D _) (t' : @Functor.CommShift C D c' _ G ℤ _ s' _),
      HEq G F ∧ ∀ n : ℤ,
        HEq (@Functor.commShiftIso C D c' _ G ℤ _ s' _ t' n)
          (@Functor.commShiftIso C D c _ F ℤ _ s _ t n) := by
  subst c'
  cases eq_of_heq hs
  exact ⟨F, t, HEq.rfl, fun _ ↦ HEq.rfl⟩

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationCategory (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E =
      ScalarLocalization.category
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E))
        (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)) := by
  rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationShift (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageShift l Ω T E)
      (sfRationalConstructibleShift l (pbcFiniteField.{u} l Ω E) T) := by
  rfl

private def familyPresentation : RationalFamily l Ω T stage := by
  have hx (E : Padic.FiniteCoefficientFields l Ω) :=
    copyShiftedFunctor _ _ _ _ (presentationCategory l Ω T E).symm (presentationShift l Ω T E).symm
      (stage E).rational.functor (stage E).shift
  choose F t ht hn using hx
  exact { functor := F, identity := ht, shift := t, shift_identity := hn }

attribute [local irreducible] familyPresentation

/-- The supplied stage functors and their entire shifts admit the named stage presentation.
Source: presentation-transport clause of the assigned raw scalar-descent argument
(blueprint: lem-fd-raw-rational-family-exists).

Proof: The named stage category and shift are the original raw category and shift,
with only their coefficient presentation changed. Record those equalities once.
Transport each supplied functor and its coherent shift along these equalities.
The transport fixes the whole functor and each shift isomorphism by HEq. Assemble
them into RationalFamily. The construction uses no scalar comparison or coherence
hypotheses and does not choose a replacement shift structure. -/
theorem rawRationalFamilyExists : Nonempty (RationalFamily l Ω T stage) :=
  ⟨familyPresentation l Ω T stage⟩

end WeilConjectures.FdRawLocalization
