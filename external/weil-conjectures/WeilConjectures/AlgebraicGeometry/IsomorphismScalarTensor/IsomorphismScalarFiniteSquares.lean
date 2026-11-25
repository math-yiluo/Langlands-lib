/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteCore
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage

/-! # Commutative squares for the finite scalar model

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

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedScalarChangeData integralScalarReductionWitness

private local instance (W : Scheme.{t}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify W

private theorem inverseSheafify_ext
    [HasWeakSheafify (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}]
    (P : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)})
    (N : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)})
    (a b : (isoSectionwiseInverseImage g AddCommGrpCat.{max u (t + 1)}).obj
      ((presheafToSheaf (ProEt.topology Y) AddCommGrpCat).obj P) ⟶ N)
    (h : ∀ U z, a.hom.app (op U)
        ((toSheafify (ProEt.topology Y) P).app
          (op ((proEtaleIsoPostcompose g).obj U)) z) =
      b.hom.app (op U)
        ((toSheafify (ProEt.topology Y) P).app
          (op ((proEtaleIsoPostcompose g).obj U)) z)) : a = b := by
  have := sectionwisePostcompose_cocontinuous g
  let e := (proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Y)
  apply (cancel_epi (e.hom.app P)).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ N.property
  change toSheafify (ProEt.topology X) ((proEtaleIsoPostcompose g).op ⋙ P) ≫
      ((e.hom.app P).hom ≫ a.hom) =
    toSheafify (ProEt.topology X) ((proEtaleIsoPostcompose g).op ⋙ P) ≫
      ((e.hom.app P).hom ≫ b.hom)
  rw [← Category.assoc, ← Category.assoc,
    (proEtaleIsoPostcompose g).toSheafify_pullbackSheafificationCompatibility]
  ext U z
  exact h U.unop z

private theorem finiteRight_ext (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
    (N : integralTowerModules l L X)
    (a b : (((restrictedRight l E L ι g n).obj P).X i) ⟶ N)
    (h : ∀ U s x, a.val.app (op U)
        (integralScalarTensorSection l E L ι Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      b.val.app (op U)
        (integralScalarTensorSection l E L ι Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x)) : a = b := by
  let e := (isoSectionwiseInverseImage g AddCommGrpCat.{max u (t + 1)}).mapIso
    ((SheafOfModules.toSheaf _).mapIso
      ((integralScalarReductionIso l E L ι Y n).app (P.X i)))
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi e.inv).1
  apply inverseSheafify_ext.{t, u} g
  intro U z
  let V := op ((proEtaleIsoPostcompose g).obj U)
  let q := (toSheafify (ProEt.topology Y)
    (SheafOfModules.changeOfRingsPresheaf (integralScalarRho l E L ι Y n)
      (P.X i)).presheaf).app V
  let fa := ((e.inv ≫ (SheafOfModules.toSheaf _).map a).hom.app (op U)).hom.comp q.hom
  let fb := ((e.inv ≫ (SheafOfModules.toSheaf _).map b).hom.app (op U)).hom.comp q.hom
  change fa z = fb z
  induction z using TensorProduct.inductionOn with
  | tmul s x => exact h U s x
  | add z w hz hw =>
      exact (_root_.map_add fa z w).trans
        ((congrArg₂ (· + ·) hz hw).trans (_root_.map_add fb z w).symm)

/--
The finite quotient and transition maps from the finite formula construction
satisfy the two naturality squares. The hypotheses include completed normalization
and the five finite formula predicates; tensor generation identifies the corresponding
natural transformations. This is strictly the square part of the finite model.
-/
theorem scalar_finite_squares
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (hb : CompletedFormula l E L ι g b)
    (hF : FiniteFormula l E L ι g bfin)
    (hL : LeftQuotientFormula l E L ι g vleft)
    (hR : RightQuotientFormula l E L ι g vright)
    (hTL : LeftTransitionFormula l E L ι g tleft)
    (hTR : RightTransitionFormula l E L ι g tright) :
    QuotientSquare l E L ι g b bfin vleft vright ∧
    TransitionSquare l E L ι g bfin tleft tright := by
  constructor
  · intro n P
    apply HomologicalComplex.hom_ext
    intro i
    apply completedScalar_tensor_ext l E L ι X
    intro U s x
    let sY := (inv (inverseImageCompletedCoefficientMap l L g)).hom.app U s
    have hs : (inverseImageCompletedCoefficientMap l L g).hom.app U sY = s :=
      congrArg (fun f ↦ (f.hom.app U).hom s)
        (IsIso.inv_hom_id (inverseImageCompletedCoefficientMap l L g))
    change (((vright n).app P).f i).val.app U
        (((b.hom.app P).f i).val.app U
          (completedScalarTensorSection l E L ι X
            (((inverseComplex l E g).obj P.obj).X i) U s x)) =
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app U
        ((((vleft n).app P).f i).val.app U
          (completedScalarTensorSection l E L ι X
            (((inverseComplex l E g).obj P.obj).X i) U s x))
    rw [← hs, hb P i U.unop sY x, hL n P i U.unop sY x,
      hR n P i U.unop sY x, hF n P i U.unop _ 1 x]
    simp only [map_one, mul_one]
    congr 1
    have hc := congrArg (fun f ↦ (f.hom.app U).hom s)
      (inverseCoefficient_square l L g n)
    change (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) sY =
      (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app U
        ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U s) at hc
    simpa only [hs, id] using hc
  · intro n P
    let e := (integralOperationsRestrict l L X (n + 1)).mapIso ((bfin (n + 1)).app P)
    have hinv (i : ℤ) (U : X.ProEt)
        (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
        (e.inv.f i).val.app (op U)
          (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
            (op ((proEtaleIsoPostcompose g).obj U)) s x) =
        doublePure l E L ι g (n + 1) P.obj i U
          ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) 1 x := by
      let z := doublePure l E L ι g (n + 1) P.obj i U
        ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) 1 x
      have hh := hF (n + 1) P i U
        ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) 1 x
      have hs := congrArg (fun f ↦ (f.hom.app (op U)).hom s)
        (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l L g (n + 1)))
      change (inv (inverseImageFiniteCoefficientMap l L g (n + 1))).hom.app (op U)
        ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) = s at hs
      simp only [map_one, id] at hh
      erw [hs] at hh
      simp only [mul_one] at hh
      have he := congrArg (fun f ↦ (f.f i).val.app (op U) z) e.hom_inv_id
      change (e.inv.f i).val.app (op U) ((e.hom.f i).val.app (op U) z) = z at he
      rw [show (e.hom.f i).val.app (op U) z = _ from hh] at he
      exact he
    apply (cancel_epi e.inv).1
    change e.inv ≫ (e.hom ≫ (tright n).app P) = _
    rw [Iso.inv_hom_id_assoc]
    apply HomologicalComplex.hom_ext
    intro i
    apply finiteRight_ext l E L ι g (n + 1) P.obj i
    intro U s x
    change (((tright n).app P).f i).val.app (op U)
        (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        ((((tleft n).app P).f i).val.app (op U)
          ((e.inv.f i).val.app (op U)
            (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
              (op ((proEtaleIsoPostcompose g).obj U)) s x)))
    rw [hinv, hTR n P i U s x]
    have ht := hTL n P i U
      ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) 1 x
    erw [ht]
    have hf := hF n P i U
      ((integralCoefficientSheafTransition l L X n).hom.app (op U)
        ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s))
      ((integralCoefficientSheafTransition l E Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) 1) x
    erw [hf]
    simp only [map_one, id]
    congr 1
    have hc := (coefficientDiagramMap l L g).naturality
      (show op (n + 1) ⟶ op n from (homOfLE (Nat.le_succ n)).op)
    simp only [Functor.comp_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at hc
    change (isoSectionwiseInverseImage g RingCat).map
        (integralCoefficientSheafTransition l L Y n) ≫
        inverseImageFiniteCoefficientMap l L g n =
      inverseImageFiniteCoefficientMap l L g (n + 1) ≫
        integralCoefficientSheafTransition l L X n at hc
    have hv := congrArg (fun f ↦ (f.hom.app (op U)).hom s) hc
    change (inverseImageFiniteCoefficientMap l L g n).hom.app (op U)
        ((integralCoefficientSheafTransition l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) =
      (integralCoefficientSheafTransition l L X n).hom.app (op U)
        ((inverseImageFiniteCoefficientMap l L g (n + 1)).hom.app (op U) s) at hv
    erw [← hv]
    have he := (congrArg (fun f ↦ (f.hom.app (op U)).hom
      ((integralCoefficientSheafTransition l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) s))
      (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l L g n))).symm
    change (integralCoefficientSheafTransition l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) s =
      (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U)
        ((inverseImageFiniteCoefficientMap l L g n).hom.app (op U)
          ((integralCoefficientSheafTransition l L Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) s)) at he
    have hi := ((integralScalarQuotientSheafMap l E L ι Y n).hom.app
      (op ((proEtaleIsoPostcompose g).obj U))).hom.map_one
    change (integralScalarQuotientSheafMap l E L ι Y n).hom.app
      (op ((proEtaleIsoPostcompose g).obj U)) 1 = 1 at hi
    erw [hi, mul_one]
    exact he

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
