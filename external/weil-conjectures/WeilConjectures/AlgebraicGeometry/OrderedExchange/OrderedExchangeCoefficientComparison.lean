/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeStrictCoefficientEquations
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeReconstructionEquations
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeRawCoefficientEquation

/-! # Assembly of the ordered coefficient comparison

## References

* Stacks Project, Tags 099M, 099N, 0A07 and 0E48
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- All specified strict coefficient, reconstruction and direct-image/limit normalizations,
including equality of the ordered maps as natural transformations on the full complete category.
-/
theorem coefficientComparison (sq : ChosenCartesianSquare g' f' f g) :
    (∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) ∧
      ((res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
          (lambda d Y').hom.app
            ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
          (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom) ∧
      ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
          (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
        (phi d g').hom.app ⟨K, hK⟩ ≫
          (reconstruction d g' ((res d X).obj K)).hom) ∧
      ((res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom ≫
          (S (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
        (iotaT (f' := f') (g' := g') d K hK).hom ≫
          (T (f' := f') (g' := g') d ((res d X).obj K)).hom)) ∧
    rawNormalized d sq = constantNormalized d sq ∧
    (∀ [IsProper f] (K : d.derived X) (hK : d.TowerComplete X K)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
      d.completedExchange sq K = d.completedBaseChangeMap sq K hK W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨h₁, h₂, h₃⟩ := strictCoefficientEquations d sq K hK
    obtain ⟨h₄, h₅, h₆, h₇⟩ := reconstructionCoefficientEquations d sq K hK
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  · apply NatTrans.ext
    funext K
    exact rawCoefficientEquation d sq K
  · intro _ K hK W
    rfl

end AlgebraicGeometry.Scheme.OrderedExchange
