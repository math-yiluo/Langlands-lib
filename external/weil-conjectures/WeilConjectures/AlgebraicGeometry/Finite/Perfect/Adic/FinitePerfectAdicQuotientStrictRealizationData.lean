/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStrictRealizationComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensorTransition
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarComponentUnderlying

/-! # The scalar realization of the strict quotient coordinates

Source: Stacks Project, Tags 03CY, 03DA, 03EK and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible finite comparisons send constant sections to the canonical constant sections.
Source: Stacks Tags 093M and 09C6.

Proof: every constant quotient section lifts to a constant section of the coefficient ring.
The scalar square of the compatibility identifies its image with the image of the completed
scalar map, whose projection is the canonical constant section. -/
theorem finitePerfectModelsCompatible_normalized (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) :
    FinitePerfectModelsNormalized X d φ := by
  intro n U c
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective c.down
  let a' : ULift.{t + 1} A := ULift.up a
  have hc : c = ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a'.down) := by
    exact (congrArg ULift.up ha).symm
  subst hc
  let J := ProEt.topology X
  have hs := (completedAdicScalar_exists X d).exists.choose_spec n U a'
  let qlift : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hq := congrArg (fun k ↦ (k.app U).hom a')
    (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a'.down)) =
    (adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
      ((koszulConstantUnit X A).app U a') at hq
  have hh := congrArg (fun k ↦ ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    k).hom.app U ((koszulConstantUnit X A).app U a')) (hcompat.2 n)
  change (completedAdicProjection X d n).hom.app U
      (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicScalar X d)).hom.app U ((koszulConstantUnit X A).app U a')) =
    (φ n).hom.app U ((adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
      ((koszulConstantUnit X A).app U a')) at hh
  rw [hq]
  exact hh.symm.trans hs

section Realization

variable (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
  (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
    completedAdicFiniteCommRing X d n)
  (hcompat : FinitePerfectModelsCompatible X d φ)
  (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)

/-- The scalar realization of the fixed-scalar coordinates of a module over the finite quotient
ring is its restriction to `W`. -/
def finitePerfectAdicQuotientRealizationIso (n : ℕ) :
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
        (completedAdicFiniteCommRing X d n) (φ n) V ⋙
      ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom ⋙
        finitePerfectAdicScalarModules X d V U W f n ≅
      SheafOfModules.restrictScalars (completedAdicProjection X d n) ⋙
        SheafOfModules.overFunctor (completedAdicRing X d) W :=
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  finitePerfectAdicRealizationIso X V U W f (completedAdicFiniteCommRing X d n) (φ n)
    (finitePerfectAdicSliceScalar X d W n)
    (fun Z c ↦ finitePerfectModelsCompatible_normalized X d φ hcompat n (op Z.left) c)
    (completedAdicProjection X d n)

/-- Forgetting along the finite projection, the ordinary scalar extension to the finite quotient
ring is the ordinary tensor product with the restricted finite quotient ring. -/
def finitePerfectAdicQuotientTensorIso (n : ℕ) :
    completedAdicChange X (completedAdicCommProjection X d n) ⋙
        SheafOfModules.restrictScalars (completedAdicProjection X d n) ≅
      completedAdicOrdinaryTower X d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (completedAdicCommRing X d)
  SheafOfModules.changeOfRingsTensorNatIso (completedAdicCommProjection X d n)
    (completedAdicChange X (completedAdicCommProjection X d n))
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose
    (completedAdicChangeData X
      (completedAdicCommProjection X d n)).choose_spec.choose_spec.choose

/-- The explicit scalar realizations carry the fixed-scalar coordinates to the strict ordinary
tensor tower restricted to `W`. -/
def finitePerfectAdicQuotientStrictRealizationIso (n : ℕ) :
    finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
          U.hom ⋙ finitePerfectAdicScalarModules X d V U W f n ≅
      completedAdicOrdinaryTower X d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n) ⋙
        SheafOfModules.overFunctor (completedAdicRing X d) W :=
  Functor.isoWhiskerLeft (completedAdicChange X (completedAdicCommProjection X d n))
      (finitePerfectAdicQuotientRealizationIso X d φ hcompat V U W f n) ≪≫
    Functor.isoWhiskerRight (finitePerfectAdicQuotientTensorIso X d n)
      (SheafOfModules.overFunctor (completedAdicRing X d) W)

/-- The commutative consecutive quotient map forgets to the finite quotient step. -/
theorem completedAdicQuotientCommMap_forget (n : ℕ) :
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) =
      completedAdicFiniteStep X d n := by
  change (completedAdicRingSystem X d).map (homOfLE (Nat.le_succ n)).op = _
  exact Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The limit projections are compatible with the consecutive quotient map. -/
theorem completedAdicProjection_comp_quotientCommMap (n : ℕ) :
    completedAdicProjection X d (n + 1) ≫
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) =
      completedAdicProjection X d n := by
  have h := congrArg (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))
  rw [Functor.map_comp] at h
  exact h

/-- The transition of restricted quotient modules is the quotient map on sections. -/
theorem completedAdicFiniteModuleStep_apply (n : ℕ) (Z : X.ProEtᵒᵖ)
    (s : (completedAdicFiniteCommRing X d (n + 1)).obj.obj Z) :
    (completedAdicFiniteModuleStep X d n).val.app Z s =
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app Z s := by
  rw [show (completedAdicFiniteModuleStep X d n).val.app Z s =
    (completedAdicFiniteStep X d n).hom.app Z s from
      (completedAdicFiniteModuleStep_exists X d n).exists.choose_spec Z s]
  rw [← completedAdicQuotientCommMap_forget X d n]
  rfl

/-- The consecutive transition of the strict ordinary tensor tower is tensor with the quotient
step. -/
theorem completedAdicOrdinaryTower_map_succ (N : CompletedAdicModules X d) (n : ℕ) :
    ((completedAdicOrdinaryTower X d).obj N).map (homOfLE (Nat.le_succ n)).op =
      N ◁ completedAdicFiniteModuleStep X d n := by
  change ((Functor.ofOpSequence
    (X := fun n ↦ (curriedTensor (CompletedAdicModules X d)).flip.obj
      (completedAdicFiniteModule X d n))
    (fun n ↦ (curriedTensor (CompletedAdicModules X d)).flip.map
      (completedAdicFiniteModuleStep X d n))).map (homOfLE (Nat.le_succ n)).op).app N = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- Under the tensor identifications, the ordinary quotient transition is the transition of the
strict ordinary tensor tower. -/
theorem finitePerfectAdicQuotientTensorIso_transition (n : ℕ) (N : CompletedAdicModules X d) :
    (SheafOfModules.restrictScalars (completedAdicProjection X d (n + 1))).map
        ((completedAdicChangeQuotientTransition X d n).app N) ≫
      (finitePerfectAdicRestrictComp (completedAdicProjection X d (n + 1)) _
        (completedAdicProjection X d n) (completedAdicProjection_comp_quotientCommMap X d n)
        ((completedAdicChange X (completedAdicCommProjection X d n)).obj N)).hom ≫
      (finitePerfectAdicQuotientTensorIso X d n).hom.app N =
    (finitePerfectAdicQuotientTensorIso X d (n + 1)).hom.app N ≫
      ((completedAdicOrdinaryTower X d).obj N).map (homOfLE (Nat.le_succ n)).op := by
  rw [completedAdicOrdinaryTower_map_succ]
  -- Fix the extension functors before comparing the generic transition with the tower.
  have h := SheafOfModules.changeOfRingsTensorNatIso_transition
    (E₂ := completedAdicChange X (completedAdicCommProjection X d (n + 1)))
    (E₃ := completedAdicChange X (completedAdicCommProjection X d n))
    (completedAdicCommProjection X d (n + 1))
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
    (completedAdicCommProjection X d n)
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))
    (completedAdicChangeData X (completedAdicCommProjection X d (n + 1))).choose_spec.choose
    (completedAdicChangeData X
      (completedAdicCommProjection X d (n + 1))).choose_spec.choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose_spec.choose
    (completedAdicFiniteModuleStep X d n) (completedAdicFiniteModuleStep_apply X d n) N
    (finitePerfectAdicRestrictComp (completedAdicProjection X d (n + 1)) _
        (completedAdicProjection X d n) (completedAdicProjection_comp_quotientCommMap X d n)
        ((completedAdicChange X (completedAdicCommProjection X d n)).obj N)) (fun _ _ ↦ rfl)
  exact h

end Realization

end AlgebraicGeometry.Scheme
