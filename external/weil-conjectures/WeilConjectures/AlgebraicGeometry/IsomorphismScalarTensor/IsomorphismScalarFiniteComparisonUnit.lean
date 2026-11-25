/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import all WeilConjectures.AlgebraicGeometry.ScalarQuotientChain.IsomorphismScalarQuotientChainSquares
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison

/-! # Unit case of the finite scalar comparison formula

This isolates the unit middle coefficient case from the general pure-tensor
formula.  It is the normalized reassociation step in the finite coefficient
calculation.

## Implementation details

The finite comparison is constructed independently of the completed comparison: it is the
(invertible) adjunction mate of the finite coefficient square, composed with scalar-extension
reassociation and lifted termwise to complexes.

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

/-- The finite formula with the middle finite coefficient specialized to `1`.
The normalized balanced reassociation sends the outer coefficient through the
finite inverse-image map and inserts the unit in the middle coefficient. -/
def FiniteFormulaUnit
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        (doublePure l E L ι g n P.obj i U s 1 x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) 1) x

open CategoryTheory.CochainPullback
open scoped ChangeOfRings

attribute [local irreducible] ScalarQuotientChain.extensionComp
  ScalarQuotientChain.adjointTransport

private def reductionPresentation (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E Y n ≅
      extensionFunctor.{max u (t + 1), t + 1, t}
        (completedIntegralCommRingProjectionUnrestricted l E Y n) :=
  NatIso.ofComponents (fun M ↦ eqToIso (unrestrictedReduction_obj l E Y n M)) (by
    intro M N f
    rw [unrestrictedReduction_map]
    simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
    rfl)

private theorem reductionPresentation_pure (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U)
    (x : M.val.obj U) :
    ((reductionPresentation l E n).hom.app M).val.app U
      (unrestrictedIntegralTensorSection l E Y n M U s x) =
        extensionTmul.{max u (t + 1), t + 1, t}
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M U s x := by
  change ((eqToHom (unrestrictedReduction_obj l E Y n M)).val.app U)
    ((eqToHom (unrestrictedReduction_obj l E Y n M).symm).val.app U _) = _
  have h := congrArg (fun f ↦ f.val.app U
    (extensionTmul.{max u (t + 1), t + 1, t}
      (completedIntegralCommRingProjectionUnrestricted l E Y n) M U s x))
    (eqToHom_trans (unrestrictedReduction_obj l E Y n M).symm
      (unrestrictedReduction_obj l E Y n M))
  exact h

attribute [local irreducible] reductionPresentation

private def finitePresentation (n : ℕ) :
    finiteExtension l E L ι X n ≅ extensionFunctor.{max u (t + 1), t + 1, t}
      (integralScalarQuotientSheafMap l E L ι X n) :=
  NatIso.ofComponents (fun M ↦ eqToIso ((finiteChangeData l E L ι X n).obj_eq M)) (by
    intro M N f
    rw [(finiteChangeData l E L ι X n).map_eq]
    simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
    rfl)

private theorem finitePresentation_pure (n : ℕ)
    (M : integralOperationsFiniteModules l E X n) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj U) (x : M.val.obj U) :
    ((finitePresentation l E L ι n).hom.app M).val.app U
      (finitePure l E L ι X n M U s x) =
        extensionTmul.{max u (t + 1), t + 1, t}
          (integralScalarQuotientSheafMap l E L ι X n) M U s x := by
  change ((eqToHom ((finiteChangeData l E L ι X n).obj_eq M)).val.app U)
    ((eqToHom ((finiteChangeData l E L ι X n).obj_eq M).symm).val.app U _) = _
  exact congrArg (fun f ↦ f.val.app U
    (extensionTmul.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι X n) M U s x))
    (eqToHom_trans ((finiteChangeData l E L ι X n).obj_eq M).symm
      ((finiteChangeData l E L ι X n).obj_eq M))

attribute [local irreducible] finitePresentation

private def scalarPresentation (n : ℕ) :
    integralScalarReduction l E L ι Y n ≅ extensionFunctor.{max u (t + 1), t + 1, t}
      (integralScalarRho l E L ι Y n) :=
  integralScalarReductionIso l E L ι Y n

private theorem finiteCoefficientSquare (n : ℕ) :
    (isoSectionwiseInverseImage g RingCat).map
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
          (integralScalarQuotientSheafMap l E L ι Y n)) ≫
        inverseImageFiniteCoefficientMap l L g n =
      inverseImageFiniteCoefficientMap l E g n ≫
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
          (integralScalarQuotientSheafMap l E L ι X n) := by
  unfold integralScalarQuotientSheafMap
  exact constantMap_naturality g _

private theorem finiteInverseSquare (n : ℕ) :
    inv (inverseImageFiniteCoefficientMap l E g n) ≫
        (isoSectionwiseInverseImage g RingCat).map
          ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
            (integralScalarQuotientSheafMap l E L ι Y n)) =
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
          (integralScalarQuotientSheafMap l E L ι X n) ≫
        inv (inverseImageFiniteCoefficientMap l L g n) := by
  apply (cancel_mono (inverseImageFiniteCoefficientMap l L g n)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [finiteCoefficientSquare l E L ι g n]
  simp only [IsIso.inv_hom_id_assoc]

private def finiteRestrictionTransport (n : ℕ) :
    restrictionFunctor.{max u (t + 1), t + 1, t, max u (t + 1)}
      (integralScalarQuotientSheafMap l E L ι Y n) ⋙
        inverseImageFiniteModules l E g n ≅
      inverseImageFiniteModules l L g n ⋙
        restrictionFunctor.{max u (t + 1), t + 1, t, max u (t + 1)}
          (integralScalarQuotientSheafMap l E L ι X n) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (X₁ := ((restrictionFunctor.{max u (t + 1), t + 1, t, max u (t + 1)}
        (integralScalarQuotientSheafMap l E L ι Y n) ⋙
        inverseImageFiniteModules l E g n).obj M).val.obj U)
      (X₂ := ((inverseImageFiniteModules l L g n ⋙
        restrictionFunctor.{max u (t + 1), t + 1, t, max u (t + 1)}
          (integralScalarQuotientSheafMap l E L ι X n)).obj M).val.obj U)
      { __ := AddEquiv.refl _
        map_smul' a x := by
          have hx := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) (finiteInverseSquare l E L ι g n)) a
          exact congrArg (fun z ↦ z • (show M.val.obj
            (op ((proEtaleIsoPostcompose g).obj U.unop)) from x)) hx })
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private def finiteScalarTransport (n : ℕ) :
    inverseImageFiniteModules l E g n ⋙
        extensionFunctor.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι X n) ≅
      extensionFunctor.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι Y n) ⋙
        inverseImageFiniteModules l L g n := by
  have := ScalarQuotientChain.sectionwiseModules_equivalence g
    (inverseImageFiniteCoefficientMap l E g n)
  have := ScalarQuotientChain.sectionwiseModules_equivalence g
    (inverseImageFiniteCoefficientMap l L g n)
  let f := ScalarQuotientChain.adjointTransport
    (extensionAdjunction (integralScalarQuotientSheafMap l E L ι Y n))
    (extensionAdjunction (integralScalarQuotientSheafMap l E L ι X n))
    (inverseImageFiniteModules l E g n) (inverseImageFiniteModules l L g n)
    (finiteRestrictionTransport l E L ι g n)
  have : IsIso f := ScalarQuotientChain.adjointTransport_isIso _ _ _ _ _
  exact asIso f

private theorem finiteScalarTransport_pure (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((finiteScalarTransport l E L ι g n).hom.app M).val.app (op U)
      (extensionTmul.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι X n)
        ((inverseImageFiniteModules l E g n).obj M) (op U) s x) =
      extensionTmul.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι Y n) M
        (op ((proEtaleIsoPostcompose g).obj U))
        ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s) x := by
  refine (ScalarQuotientChain.transpose_pure _ _ _
    ((finiteScalarTransport l E L ι g n).hom.app M) (op U) s x).trans ?_
  have hh := ScalarQuotientChain.adjointTransport_transpose
    (extensionAdjunction (integralScalarQuotientSheafMap l E L ι Y n))
    (extensionAdjunction (integralScalarQuotientSheafMap l E L ι X n))
    (inverseImageFiniteModules l E g n) (inverseImageFiniteModules l L g n)
    (finiteRestrictionTransport l E L ι g n) M
  have hx := congrArg (fun f ↦ f.val.app (op U) x) hh
  change (((extensionAdjunction (integralScalarQuotientSheafMap l E L ι X n)).homEquiv _ _
    ((finiteScalarTransport l E L ι g n).hom.app M)).val.app (op U) x) =
      ((extensionAdjunction (integralScalarQuotientSheafMap l E L ι Y n)).unit.app M).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) x at hx
  erw [hx]
  have hu := (Classical.choose_spec
    (extensionAdjunction_existsUnique (integralScalarQuotientSheafMap l E L ι Y n))).1 M
      (op ((proEtaleIsoPostcompose g).obj U)) x
  change ((extensionAdjunction (integralScalarQuotientSheafMap l E L ι Y n)).unit.app M).val.app
    _ x = _ at hu
  rw [hu]
  exact (ScalarQuotientChain.pure_smul _ M _ _ x).symm

attribute [local irreducible] finiteScalarTransport finiteRestrictionTransport

private def finiteModuleComparison (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E Y n ⋙ inverseImageFiniteModules l E g n ⋙
        finiteExtension l E L ι X n ≅
      integralScalarReduction l E L ι Y n ⋙ inverseImageFiniteModules l L g n :=
  Functor.isoWhiskerLeft
      (unrestrictedIntegralReductionFunctor l E Y n ⋙ inverseImageFiniteModules l E g n)
      (finitePresentation l E L ι n) ≪≫
    Functor.isoWhiskerRight (reductionPresentation l E n)
      (inverseImageFiniteModules l E g n ⋙
        extensionFunctor.{max u (t + 1), t + 1, t} (integralScalarQuotientSheafMap l E L ι X n)) ≪≫
    Functor.isoWhiskerLeft (extensionFunctor.{max u (t + 1), t + 1, t}
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
      (finiteScalarTransport l E L ι g n) ≪≫
    Functor.isoWhiskerRight (ScalarQuotientChain.extensionComp
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (integralScalarQuotientSheafMap l E L ι Y n)
      (integralScalarRho l E L ι Y n) rfl) (inverseImageFiniteModules l L g n) ≪≫
    Functor.isoWhiskerRight (scalarPresentation l E L ι n).symm
      (inverseImageFiniteModules l L g n)

private theorem finiteCanonical_map_pure (n : ℕ)
    {M N : integralOperationsFiniteModules l E X n} (f : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj U) (x : M.val.obj U) :
    ((extensionFunctor.{max u (t + 1), t + 1, t}
      (integralScalarQuotientSheafMap l E L ι X n)).map f).val.app U
      (extensionTmul.{max u (t + 1), t + 1, t}
        (integralScalarQuotientSheafMap l E L ι X n) M U s x) =
    extensionTmul.{max u (t + 1), t + 1, t}
      (integralScalarQuotientSheafMap l E L ι X n) N U s (f.val.app U x) := by
  let a := integralScalarQuotientSheafMap l E L ι X n
  let c : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} a M ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} a N :=
    { app := fun V ↦ (ModuleCat.extendScalars (a.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality a M f }
  have h := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).obj
      (integralCoefficientCommRingSheaf l L X n)).obj)).unit.naturality c
  have hh := congrArg (fun k ↦ k.app U
    (s ⊗ₜ[(integralCoefficientCommRingSheaf l E X n).obj.obj U,
      (a.hom.app U).hom] x)) h
  change extensionTmul.{max u (t + 1), t + 1, t} a N U s (f.val.app U x) =
    ((extensionFunctor.{max u (t + 1), t + 1, t}
      a).map f).val.app U (extensionTmul.{max u (t + 1), t + 1, t} a M U s x) at hh
  exact hh.symm

private theorem finiteModuleComparison_pure (n : ℕ) (M : integralTowerModules l E Y)
    (U : X.ProEt) (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((finiteModuleComparison l E L ι g n).hom.app M).val.app (op U)
      (finitePure l E L ι X n
        ((inverseImageFiniteModules l E g n).obj
          ((unrestrictedIntegralReductionFunctor l E Y n).obj M)) (op U) s
        (unrestrictedIntegralTensorSection l E Y n M
          (op ((proEtaleIsoPostcompose g).obj U)) a x)) =
      integralScalarTensorSection l E L ι Y n M
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) a) x := by
  change ((scalarPresentation l E L ι n).inv.app M).val.app
    (op ((proEtaleIsoPostcompose g).obj U))
    (((ScalarQuotientChain.extensionComp
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (integralScalarQuotientSheafMap l E L ι Y n)
      (integralScalarRho l E L ι Y n) rfl).hom.app M).val.app
      (op ((proEtaleIsoPostcompose g).obj U))
      (((finiteScalarTransport l E L ι g n).hom.app
        ((extensionFunctor.{max u (t + 1), t + 1, t}
          (completedIntegralCommRingProjectionUnrestricted l E Y n)).obj M)).val.app (op U)
        (((extensionFunctor.{max u (t + 1), t + 1, t}
          (integralScalarQuotientSheafMap l E L ι X n)).map
          ((inverseImageFiniteModules l E g n).map
            ((reductionPresentation l E n).hom.app M))).val.app (op U)
          (((finitePresentation l E L ι n).hom.app _).val.app (op U)
            (finitePure l E L ι X n _ (op U) s
              (unrestrictedIntegralTensorSection l E Y n M
                (op ((proEtaleIsoPostcompose g).obj U)) a x)))))) = _
  rw [finitePresentation_pure, finiteCanonical_map_pure]
  change ((scalarPresentation l E L ι n).inv.app M).val.app
    (op ((proEtaleIsoPostcompose g).obj U))
    (((ScalarQuotientChain.extensionComp
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (integralScalarQuotientSheafMap l E L ι Y n)
      (integralScalarRho l E L ι Y n) rfl).hom.app M).val.app
      (op ((proEtaleIsoPostcompose g).obj U))
      (((finiteScalarTransport l E L ι g n).hom.app
        ((extensionFunctor.{max u (t + 1), t + 1, t}
          (completedIntegralCommRingProjectionUnrestricted l E Y n)).obj M)).val.app (op U)
        (extensionTmul.{max u (t + 1), t + 1, t}
          (integralScalarQuotientSheafMap l E L ι X n)
          ((inverseImageFiniteModules l E g n).obj
            ((extensionFunctor.{max u (t + 1), t + 1, t}
              (completedIntegralCommRingProjectionUnrestricted l E Y n)).obj M)) (op U) s
          (((reductionPresentation l E n).hom.app M).val.app
            (op ((proEtaleIsoPostcompose g).obj U))
            (unrestrictedIntegralTensorSection l E Y n M
              (op ((proEtaleIsoPostcompose g).obj U)) a x))))) = _
  rw [reductionPresentation_pure, finiteScalarTransport_pure]
  have h := ScalarQuotientChain.extensionComp_pure
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (integralScalarQuotientSheafMap l E L ι Y n)
    (integralScalarRho l E L ι Y n) rfl M (op ((proEtaleIsoPostcompose g).obj U))
    (@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
      ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) a x
  exact congrArg (((scalarPresentation l E L ι n).inv.app M).val.app
    (op ((proEtaleIsoPostcompose g).obj U))) h

attribute [local irreducible] finiteModuleComparison

private def finiteChainComparison (n : ℕ) :
    finiteLeft l E L ι g n ≅ finiteRight l E L ι g n := by
  let : (finiteExtension l E L ι X n).Additive :=
    (finiteChangeData l E L ι X n).additive
  exact NatIso.mapHomologicalComplex (finiteModuleComparison l E L ι g n) (.up ℤ)

/-- A normalized completed comparison `b` admits finite balanced comparisons at every level
satisfying the unit pure-tensor formula `FiniteFormulaUnit`. -/
theorem finite_formula_unit_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n,
      FiniteFormulaUnit l E L ι g bfin := by
  have _ := hb
  refine ⟨fun n ↦ Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
    (finiteChainComparison l E L ι g n), ?_⟩
  intro n P i U s x
  exact finiteModuleComparison_pure l E L ι g n (P.obj.X i) U s 1 x

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
