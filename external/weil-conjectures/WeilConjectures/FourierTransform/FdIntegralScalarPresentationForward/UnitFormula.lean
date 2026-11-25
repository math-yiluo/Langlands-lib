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

/-! # Units of the normalized derived ordinary square

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

set_option linter.unusedSectionVars false in
/-- The normalized derived ordinary square is compatible with the units. -/
private theorem eD_unit (E : Padic.FiniteCoefficientFields l Ω)
    (o : FdOrdinaryScalarTransport l Ω T (le_refl E))
    (Y : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) T)) :
    (FdIntegralScalarForward.eD l Ω T (le_refl E) o).inv.app Y ≫
        (integralDetailedTransport T l _).map
          (eqToHom (Functor.congr_obj (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l
            (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E) ι T)
            (FdIntegralScalarForward.inclusion_id l Ω E).symm).symm Y) ≫
            (integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app Y) =
      (pbcAmbientScalarUnit l Ω T E).hom.app ((integralDetailedTransport T l _).obj Y) := by
  refine FdIntegralScalarForward.unit_generic
    (C := scalarReductionSource l (pbcFiniteField.{u} l Ω E) T)
    (aC := @SheafOfModules.instAbelian _ _ _ _
      (@GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat _ _ _ T) (sfAbBijective T))
    (dC := scalarReductionSourceDerived l (pbcFiniteField.{u} l Ω E) T)
    (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E) ι T)
    (hFa := fun ι ↦ integralOrdinaryScalar_additive l _ _ ι T)
    (hFl := fun ι ↦ integralOrdinaryScalar_finiteLimits l _ _ ι T)
    (hFc := fun ι ↦ integralOrdinaryScalar_finiteColimits l _ _ ι T)
    _ _ (FdIntegralScalarForward.inclusion_id l Ω E)
    (integralOrdinaryScalarUnit l (pbcFiniteField.{u} l Ω E) T)
    (integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteFieldInclusion l Ω (le_refl E)) T)
    (integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E)
      (AlgHom.id ℚ_[l] _) T) ?_ ?_
    (integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T) ?_
    ((integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteFieldInclusion l Ω (le_refl E)) T).mapHomologicalComplex (.up ℤ)) ?_
    (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteFieldInclusion l Ω (le_refl E)) T).mapDerivedCategoryFactors ?_
    (NatIso.mapHomologicalComplex (FdIntegralScalarForward.Ounit l Ω T E) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)) ?_
    DerivedCategory.Q _ _ _ _ _ _ _ _ (FdIntegralScalarForward.eD l Ω T (le_refl E) o) _
    (FdIntegralScalarForward.eD_heh l Ω T (le_refl E) o)
    (FdIntegralScalarForward.ambient_unit_rep l Ω T E)
    (FdIntegralScalarForward.ordinary_unit_chain l Ω T E o)
    (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) ι T) (FdIntegralScalarForward.inclusion_id l Ω E).symm).symm Y
  all_goals rfl

end Atoms

end WeilConjectures
