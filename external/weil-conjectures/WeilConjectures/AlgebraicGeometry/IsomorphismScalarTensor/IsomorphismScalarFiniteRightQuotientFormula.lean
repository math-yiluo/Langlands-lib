/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison

/-! # Right finite scalar quotient formula

This is the right half of the finite quotient construction.

## Implementation details

The right half is separated from the left map because its unit insertion is formed before
inverse image and therefore has an independent pure-tensor calculation. The quotient maps are
the completed scalar quotient maps followed by completed inverse image; they do not depend on
the completed comparison.

## References

* Stacks Project, Tags 03EK and 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness
  completedIntegralCoefficientSheafUnrestricted

private def rightModuleQuotient (n : ℕ) :
    completedOrdinaryScalarExtension l E L ι Y ⋙ inverseImageIntegralModules l L g ⟶
      integralScalarReduction l E L ι Y n ⋙ inverseImageFiniteModules l L g n ⋙
        SheafOfModules.restrictScalars (coefficientProjection l L X n) :=
  Functor.whiskerRight
    (show completedOrdinaryScalarExtension l E L ι Y ⟶
        integralScalarReduction l E L ι Y n ⋙
          SheafOfModules.restrictScalars (coefficientProjection l L Y n) from
      { app := fun M ↦ completedScalarModuleArrow l E L ι Y M n
        naturality := fun _ _ f ↦ completedScalarModuleArrow_naturality l E L ι Y f n })
    (inverseImageIntegralModules l L g) ≫
      Functor.whiskerLeft (integralScalarReduction l E L ι Y n)
        (inverseReductionTransport l L g n)

private def rightComplexQuotient (n : ℕ) :
    rightComplex l E L ι g ⟶ restrictedRight l E L ι g n where
  app P :=
    { f := fun i ↦ (rightModuleQuotient l E L ι g n).app (P.X i)
      comm' := fun i j _ ↦ ((rightModuleQuotient l E L ι g n).naturality
        (P.d i j)).symm }
  naturality := by
    intro P Q f
    ext i : 1
    exact (rightModuleQuotient l E L ι g n).naturality (f.f i)

/-- For a normalized completed comparison `b`, there are right completed-to-finite quotient
maps at every level satisfying the pure-tensor formula `RightQuotientFormula`. -/
theorem right_quotient_formula_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n,
      RightQuotientFormula l E L ι g vright := by
  have _ := hb
  refine ⟨fun n ↦ Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι
    (rightComplexQuotient l E L ι g n), ?_⟩
  intro n P i U s x
  exact completedScalarModuleArrow_tensor l E L ι Y (P.obj.X i) n
    (op ((proEtaleIsoPostcompose g).obj U)) s x

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
