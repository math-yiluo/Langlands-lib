/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteComparisonFormula
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Finite scalar transition formulas

This is the adjacent-transition component of the finite scalar model.  It is
split from the finite comparison and quotient-map constructions.

## References

* Stacks Project, Tags 03EK and 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

private def rightRestrictionIso (n : ℕ) :
    integralScalarLevel l E L ι Y n ⋙ inverseComplex l L g ≅
      restrictedRight l E L ι g n := by
  let α := inverseReductionTransport l L g n
  haveI : ∀ N, IsIso (α.app N) := fun N ↦ by
    have : IsIso ((SheafOfModules.toSheaf _).map (α.app N)) := by
      change IsIso (𝟙 _)
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft (integralScalarReduction l E L ι Y n) (asIso α)) (.up ℤ)

private theorem rightRestrictionIso_hom_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : X.ProEt)
    (z : (((restrictedRight l E L ι g n).obj P).X i).val.obj (op U)) :
    (((rightRestrictionIso l E L ι g n).hom.app P).f i).val.app (op U) z = z := rfl

private theorem rightRestrictionIso_inv_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : X.ProEt)
    (z : (((restrictedRight l E L ι g n).obj P).X i).val.obj (op U)) :
    (((rightRestrictionIso l E L ι g n).inv.app P).f i).val.app (op U) z = z := by
  have h := congrArg (fun f ↦ (f.f i).val.app (op U) z)
    ((rightRestrictionIso l E L ι g n).hom_inv_id_app P)
  exact h

private def rightTransition (n : ℕ) :
    restrictedRight l E L ι g (n + 1) ⟶ restrictedRight l E L ι g n :=
  (rightRestrictionIso l E L ι g (n + 1)).inv ≫
    Functor.whiskerRight (integralScalarTransition l E L ι Y n) (inverseComplex l L g) ≫
      (rightRestrictionIso l E L ι g n).hom

private theorem rightTransition_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((rightTransition l E L ι g n).app P).f i).val.app (op U)
      (integralScalarTensorSection l E L ι Y (n + 1) (P.X i)
        (op ((proEtaleIsoPostcompose g).obj U)) s x) =
    integralScalarTensorSection l E L ι Y n (P.X i)
      (op ((proEtaleIsoPostcompose g).obj U))
      ((integralCoefficientSheafTransition l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) s) x := by
  unfold rightTransition
  change (((rightRestrictionIso l E L ι g n).hom.app P).f i).val.app (op U)
    ((((integralScalarTransition l E L ι Y n).app P).f i).val.app
      (op ((proEtaleIsoPostcompose g).obj U))
      ((((rightRestrictionIso l E L ι g (n + 1)).inv.app P).f i).val.app (op U) _)) = _
  rw [rightRestrictionIso_hom_apply, rightRestrictionIso_inv_apply]
  exact (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
    P i (op ((proEtaleIsoPostcompose g).obj U)) s x

attribute [local irreducible] rightRestrictionIso rightTransition

private theorem inverseFiniteTransition_apply (n : ℕ) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L X (n + 1)).obj.obj (op U)) :
    (integralCoefficientSheafTransition l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        ((inv (inverseImageFiniteCoefficientMap l L g (n + 1))).hom.app (op U) s) =
      (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U)
        ((integralCoefficientSheafTransition l L X n).hom.app (op U) s) := by
  have h := (coefficientDiagramMap l L g).naturality (homOfLE (Nat.le_succ n)).op
  have h' :
      inv (inverseImageFiniteCoefficientMap l L g (n + 1)) ≫
          (isoSectionwiseInverseImage g RingCat).map
            (integralCoefficientSheafTransition l L Y n) =
        integralCoefficientSheafTransition l L X n ≫
          inv (inverseImageFiniteCoefficientMap l L g n) := by
    apply (cancel_mono (inverseImageFiniteCoefficientMap l L g n)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp only [Functor.comp_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    change (isoSectionwiseInverseImage g RingCat).map
        (integralCoefficientSheafTransition l L Y n) ≫
          inverseImageFiniteCoefficientMap l L g n =
        inverseImageFiniteCoefficientMap l L g (n + 1) ≫
          integralCoefficientSheafTransition l L X n at h
    rw [h, IsIso.inv_hom_id_assoc]
  exact congrArg (fun f ↦ f.hom.app (op U) s) h'

/--
The adjacent transition maps on the two finite scalar models exist and satisfy
their local formulas.
-/
theorem transition_formulas_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n,
      LeftTransitionFormula l E L ι g tleft ∧
    ∃ tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n,
      RightTransitionFormula l E L ι g tright := by
  obtain ⟨bfin, hfin⟩ := finite_formula_exists l E L ι g b hb
  let e n := Functor.isoWhiskerRight (bfin n) (integralOperationsRestrict l L X n)
  let tright n := Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι
    (rightTransition l E L ι g n)
  let tleft n := (e (n + 1)).hom ≫ tright n ≫ (e n).inv
  refine ⟨tleft, ?_, tright, ?_⟩
  · intro n P i U s a x
    have hcoef :
        (integralCoefficientSheafTransition l L Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U))
            ((@id ((integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
                (op ((proEtaleIsoPostcompose g).obj U)))
              ((inv (inverseImageFiniteCoefficientMap l L g (n + 1))).hom.app (op U) s)) *
              (integralScalarQuotientSheafMap l E L ι Y (n + 1)).hom.app
                (op ((proEtaleIsoPostcompose g).obj U)) a) =
          (@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
              (op ((proEtaleIsoPostcompose g).obj U)))
            ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U)
              ((integralCoefficientSheafTransition l L X n).hom.app (op U) s))) *
              (integralScalarQuotientSheafMap l E L ι Y n).hom.app
                (op ((proEtaleIsoPostcompose g).obj U))
                ((integralCoefficientSheafTransition l E Y n).hom.app
                  (op ((proEtaleIsoPostcompose g).obj U)) a) := by
      rw [map_mul]
      apply congrArg₂ (· * ·)
      · exact inverseFiniteTransition_apply l L g n U s
      · exact congrArg
          (fun f ↦ f.hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
          (integralScalarQuotientSheafMap_transition l E L ι Y n)
    change ((((e n).inv.app P).f i).val.app (op U))
      ((((rightTransition l E L ι g n).app P.obj).f i).val.app (op U)
        (((((e (n + 1)).hom.app P).f i).val.app (op U))
          (doublePure l E L ι g (n + 1) P.obj i U s a x))) = _
    rw [show ((((e (n + 1)).hom.app P).f i).val.app (op U))
        (doublePure l E L ι g (n + 1) P.obj i U s a x) = _ from
      hfin (n + 1) P i U s a x]
    rw [rightTransition_apply, hcoef]
    have hh := hfin n P i U
      ((integralCoefficientSheafTransition l L X n).hom.app (op U) s)
      ((integralCoefficientSheafTransition l E Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) a) x
    have hi := congrArg (fun f ↦ (f.f i).val.app (op U)
      (doublePure l E L ι g n P.obj i U
        ((integralCoefficientSheafTransition l L X n).hom.app (op U) s)
        ((integralCoefficientSheafTransition l E Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) a) x)) ((e n).hom_inv_id_app P)
    exact (congrArg (fun z ↦ (((e n).inv.app P).f i).val.app (op U) z) hh).symm.trans hi
  · intro n P i U s x
    exact rightTransition_apply l E L ι g n P.obj i U s x

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
