/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AmbientAssociator
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractAssembly
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.RepresentativeFormula
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.UnitAssembly
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.LiftAssembly
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.GoodRepresentative
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel

/-! # The representative formula of the integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

section Atoms

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
  (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    FdOrdinaryScalarTransport l Ω T h)

set_option linter.style.haveILetI false in
/-- On every integral object the comparison is the inverse derived ordinary square followed
by the normalized ordinary-to-completed comparison. -/
private theorem lift_formula
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b)
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((b h).hom.app K).hom ≫ (eqToIso (stage L).integral_identity).hom.app ((U l Ω T h).obj K) =
      (pbcAmbientScalarExtension l Ω T h).map ((eqToIso (stage E).integral_identity).hom.app K) ≫
        (FdIntegralScalarForward.eD l Ω T h (ordinary h)).inv.app K.obj ≫
        (integralDetailedTransport T l _).map
          ((sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T).hom.app K) := by
  letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
  letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω L) T
  letI := pbcExtend_additive (pbcCompletedScalarMap l Ω T h)
  exact FdIntegralScalarForward.lift_generic DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q (sfIntegralConstructible l _ T)
    (sfIntegralConstructible l _ T) _ _ (I l Ω T stage E) (I l Ω T stage L)
    (integralDetailedTransport T l _) (integralDetailedTransport T l _)
    (stage E).integral_identity (stage L).integral_identity _ _
    (pbcAmbientScalarExtension l Ω T h) _ (b h) _ (FdIntegralScalarForward.eD l Ω T h (ordinary h))
    (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T)
    (integralOperationsGoodComplex l _ T)
    (integralScalarComplexFunctor l _ _ (pbcFiniteFieldInclusion l Ω h) T)
    (integralScalarExtensionComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T)
    ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex (.up ℤ))
    ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T).mapHomologicalComplex (.up ℤ))
    ((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ))
    (fdCoefficientTransportFactors l _ T) (fdCoefficientTransportFactors l _ T)
    (pbcComplexCounit (pbcCompletedScalarMap l Ω T h)) (fun P ↦ (ordinary h).completion l Ω P)
    ((integralOrdinaryScalar l _ _ (pbcFiniteFieldInclusion l Ω h) T).mapHomologicalComplex
      (.up ℤ))
    (integralOrdinaryScalar l _ _ (pbcFiniteFieldInclusion l Ω h) T).mapDerivedCategoryFactors
    (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h (ordinary h))
    (integralScalarCompletionChain l _ _ (pbcFiniteFieldInclusion l Ω h) T)
    (FdIntegralScalarForward.eD_fac l Ω T h (ordinary h))
    (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex_completion l Ω T h (ordinary h))
    (fun V hV ↦ (sfIntegralOrdinaryComparison_existsUnique l _ _ (pbcFiniteFieldInclusion l Ω h)
      T).exists.choose_spec V hV)
    (fun V hV ↦ hlift h V hV) (sfIntegralConstructible_goodRepresentative l _ T) K

end Atoms

end WeilConjectures
