/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientStrictRealizationData

/-! # The scalar realization of the ordinary quotient arrows

Source: Stacks Project, Tags 03CY, 03DA, 03EK and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

-- Instantiating the generic realization square unfolds the completed coefficient rings.
/-- The explicit scalar realizations carry the ordinary quotient arrows to the transition maps of
the strict ordinary tensor tower restricted to `W`, compatibly with the inverse-image comparison
and the ordinary scalar compositor.
Source: Stacks Project, Tags 03CY, 03DA and 09C6.

Proof: the quotient arrow is the ordinary quotient transition, by uniqueness on pure tensors.
The generic realization square identifies its realization with the restriction of the
transition to `W`, and under the tensor identifications the transition is the tower map. -/
theorem finitePerfectAdicQuotientStrictRealizationIso_square
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale)
    (δ : ∀ n : ℕ, finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : ∀ n : ℕ, FinitePerfectAdicQuotientTransition X d φ V n (δ n))
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)
    (n : ℕ) (N : CompletedAdicModules X d) :
    (finitePerfectAdicScalarModules X d V U W f (n + 1)).map
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) U.hom).map
            ((δ n).app N) ≫
          (finitePerfectAdicPullbackRestrictComparison U.hom (RingHom.ulift.{t + 1, t + 1}
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
            ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
      (finitePerfectAdicScalarModulesCoherence X d V U W f n).hom.app
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).obj
            ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
      (finitePerfectAdicQuotientStrictRealizationIso X d φ hcompat V U W f n).hom.app N =
    (finitePerfectAdicQuotientStrictRealizationIso X d φ hcompat V U W f (n + 1)).hom.app N ≫
      (SheafOfModules.overFunctor (completedAdicRing X d) W).map
        (((completedAdicOrdinaryTower X d).obj N).map (homOfLE (Nat.le_succ n)).op) := by
  have hδe : δ n = finitePerfectAdicQuotientStrictTransition X d φ hcompat V n :=
    finitePerfectAdicQuotientTransition_unique X d φ V n _ _ (hδ n)
      (fun N _ b x ↦ completedAdicChangeQuotientTransition_tensor X d n N _ b x)
  rw [hδe]
  have := finitePerfectAdicSliceScalar_injective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_surjective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  have hcoh : ∀ G, (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
      ((finitePerfectAdicScalarModulesCoherence X d V U W f n).hom.app G)) =
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociatedCoherence (finitePerfectAdicSliceScalar X d W (n + 1))
          (finitePerfectAdicSliceScalar X d W n)
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
            (completedAdicFiniteStep X d n))
          (finitePerfectAdicSliceScalar_step X d W n)).hom.app
          ((finitePerfectAdicChartSlice X V U W f _).obj G))) := by
    intro G
    have h := finitePerfectAdicScalarComponent_forget X d V U W f n G
    dsimp only at h
    exact congrArg (fun k ↦ k.hom) h
  have hsquare := finitePerfectAdicRealization_square_comp X V U W f
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) (φ (n + 1)) (φ n)
    (finitePerfectAdicSliceScalar X d W (n + 1)) (finitePerfectAdicSliceScalar X d W n)
    (fun Z c ↦ finitePerfectModelsCompatible_normalized X d φ hcompat (n + 1) (op Z.left) c)
    (fun Z c ↦ finitePerfectModelsCompatible_normalized X d φ hcompat n (op Z.left) c)
    (completedAdicFiniteStep X d n) (completedAdicQuotientCommMap_forget X d n)
    (finitePerfectAdicSliceScalar_step X d W n)
    (completedAdicProjection X d (n + 1)) (completedAdicProjection X d n)
    (completedAdicProjection_comp_quotientCommMap X d n)
    (finitePerfectAdicScalarModulesCoherence X d V U W f n) hcoh
    ((completedAdicChangeQuotientTransition X d n).app N)
    ((finitePerfectAdicQuotientStrictTransition X d φ hcompat V n).app N) (fun _ _ ↦ rfl)
    ((finitePerfectAdicQuotientTensorIso X d (n + 1)).app N)
    ((finitePerfectAdicQuotientTensorIso X d n).app N) _
    (finitePerfectAdicQuotientTensorIso_transition X d n N)
  dsimp only [finitePerfectAdicQuotientStrictRealizationIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, finitePerfectAdicQuotientRealizationIso]
  simpa only [← finitePerfectAdicScalarModules_eq, Iso.app_hom,
    finitePerfectAdicQuotientStrictCoordinates, Functor.comp_obj] using hsquare

end AlgebraicGeometry.Scheme
