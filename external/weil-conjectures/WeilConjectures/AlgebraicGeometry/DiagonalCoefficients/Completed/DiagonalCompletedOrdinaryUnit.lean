/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Ordinary realization of the completed coefficient unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  purZlReduction sfbConstantRingAbIso

private theorem constantRingAb_isMonHom (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    @IsMonHom _ _ _ _ _
      (Sheaf.monObj_sheafCompose_obj (Scheme.ProEt.topology X)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)))
      ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of A)) (sfbConstantRingAbIso X A).hom := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj A
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf J CommRingCat.{u + 1}).obj A)
  let g : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ S.obj :=
    Functor.whiskerRight (toSheafify J P) (forget₂ CommRingCat RingCat)
  let f := (presheafToSheaf J Ab.{u + 1}).map
      (Functor.whiskerRight g (forget₂ RingCat Ab)) ≫
    (Sheaf.sheafifyRingPresheafIso J S).hom
  have hf : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of A)) _ f := by
    have hc : IsMonHom f := by dsimp only [f]; infer_instance
    rw [constantSheafRingMonObj]
    exact IsMonHom.of_eq f rfl rfl
  have he : f = (sfbConstantRingAbIso X A).inv := by
    apply (cancel_mono (sfbConstantRingAbIso X A).hom).mp
    rw [Iso.inv_hom_id]
    let adj := sheafificationAdjunction J Ab.{u + 1}
    apply (adj.homEquiv _ _).injective
    have hg : adj.homEquiv _ _ f =
        Functor.whiskerRight g (forget₂ RingCat Ab) := by
      dsimp only [f]
      rw [adj.homEquiv_naturality_left]
      have hc : adj.homEquiv _ _ (Sheaf.sheafifyRingPresheafIso J S).hom = 𝟙 _ := by
        exact adj.right_triangle_components _
      rw [hc, Category.comp_id]
    rw [adj.homEquiv_naturality_right, hg]
    change Functor.whiskerRight g (forget₂ RingCat Ab) ≫
      (sfbConstantRingAbIso X A).hom.hom = toSheafify J _
    ext V x
    exact constantRingAb_unit X A V x
  rw [he] at hf
  exact monHomInvExplicit _ _ (sfbConstantRingAbIso X A).symm hf

private abbrev completedAbFunctor (X : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})

private noncomputable instance completedAbMon (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    MonObj ((completedAbFunctor X).obj R) :=
  Sheaf.monObj_sheafCompose_obj (Scheme.ProEt.topology X)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private def unitRealizationIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (e : CompletedRealization l X) :
    (completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l) ≅
      condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
  (e.underlying.app (SheafOfModules.unit
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))).symm ≪≫
      (Mod.forget _).mapIso e.unitIso

private theorem unitRealization_one (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (e : CompletedRealization l X) :
    η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] ≫
      (unitRealizationIso l X e).hom =
        η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] := by
  let v := unitRealizationIso l X e
  have hi : η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] ≫ v.inv =
      η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] := by
    apply (isLimitOfPreserves (completedAbFunctor X)
      (limit.isLimit (Scheme.purTwistZlTower X l))).hom_ext
    intro n
    let Rn := (sfbConstantRing X).obj ((sfbZModCoefficientTower l).obj (op (n.unop + 1)))
    let : MonObj Rn.X := Rn.mon
    let c : (completedAbFunctor X).obj (Scheme.purTwistFiniteRing X l n.unop) ≅ Rn.X :=
      sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))))
    apply (cancel_mono c.hom).mp
    have hn := eq_of_heq (e.unit_normalization n.unop)
    change v.hom ≫ (purZlReduction l X (n.unop + 1)).hom =
      (completedAbFunctor X).map (Scheme.purTwistZlProjection X l n.unop) ≫ c.hom at hn
    change (η[_] ≫ v.inv) ≫
        (completedAbFunctor X).map (Scheme.purTwistZlProjection X l n.unop) ≫ c.hom =
      η[_] ≫ (completedAbFunctor X).map
        (Scheme.purTwistZlProjection X l n.unop) ≫ c.hom
    have : IsMonHom c.hom := constantRingAb_isMonHom X _
    have : IsMonHom ((completedAbFunctor X).map
        (Scheme.purTwistZlProjection X l n.unop)) := by
      dsimp only [completedAbFunctor, Functor.comp_map, completedAbMon]
      infer_instance
    calc
      _ = η[_] ≫ v.inv ≫ (v.hom ≫ (purZlReduction l X (n.unop + 1)).hom) := by
        rw [hn]
        simp only [Category.assoc]
      _ = η[_] ≫ (purZlReduction l X (n.unop + 1)).hom := by
        rw [Iso.inv_hom_id_assoc]
      _ = η[_] := IsMonHom.one_hom (f := (purZlReduction l X (n.unop + 1)).hom)
      _ = _ := by rw [← Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (congrArg (fun k ↦ k ≫ v.hom) hi).symm

private theorem unitRealization_inv_one (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (e : CompletedRealization l X) :
    η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] ≫
      (unitRealizationIso l X e).inv =
        η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] := by
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (congrArg (fun k ↦ k ≫ (unitRealizationIso l X e).inv)
      (unitRealization_one l X e)).symm

private theorem completedPushUnit_one (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    η[(completedAbFunctor S).obj (Scheme.purTwistZlCompletion S l)] ≫
        (SheafOfModules.toSheaf
          (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).map
            (DiagonalTrace.completedPushUnit l f) =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
        (lowerStar Ab.{u + 1} f).map
          η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] := by
  let J := Scheme.ProEt.topology S
  let K := Scheme.ProEt.topology X
  let F := Scheme.proEtaleBaseChange f
  let RS := Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)
  let RX := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
  let α : RS ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
      (Scheme.proEtaleModuleCoefficients
        ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
          (Scheme.purTwistZlCompletion S l))) :=
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app
        (Scheme.purTwistZlCompletion S l)).hom (forget₂ CommRingCat RingCat)⟩
  let φ := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (diagonalCompletedCoefficientMap l f)
  let ρ := α ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map φ
  have hv : (SheafOfModules.toSheaf RS).map (DiagonalTrace.completedPushUnit l f) =
      (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map ρ := by
    ext V x
    simp only [DiagonalTrace.completedPushUnit, id_eq]
    erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  have hh : @IsMonHom _ _ _ _ _ (completedAbMon S _)
      ((lowerStar Ab.{u + 1} f).monObjObj
        ((completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)))
      ((SheafOfModules.toSheaf RS).map (DiagonalTrace.completedPushUnit l f)) := by
    rw [hv]
    have he := Sheaf.monObjObj_sheafPushforwardContinuous_eq
      (J := J) (K := K) F RX
    have ht : (lowerStar Ab.{u + 1} f).monObjObj
        ((completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)) =
      Sheaf.monObj_sheafCompose_obj J
        ((F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX) := by
      convert! he using 1
    rw [ht]
    dsimp only [completedAbMon, completedAbFunctor, Functor.comp_obj]
    infer_instance
  exact hh.one_hom

-- The normalized sheaf comparisons require several large definitional conversions.
/-- Ordinary realization carries the actual completed unit map to the coefficient unit.
Source: diagonal tower coefficient changes (1), the normalized unital coefficient maps.
(blueprint: lem-diagonal-completed-ordinary-unit).

Proof: maps out of the regular module are determined by their value on coefficient one.
The unit normalization, tested at every finite coefficient projection, shows that each
realization unit isomorphism takes completed coefficient one to condensed coefficient one.
Indeed the finite projections jointly detect equality in the actual completed coefficient
limit. The ordinary square preserves underlying sections, and the actual completed
coefficient map and the condensed structural map both preserve one. Thus the two maps
have the same value on one and coincide. This works on the empty scheme as well. -/
theorem completed_ordinary_unit
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eY : CompletedRealization l Y) (eP : CompletedRealization l (ProjectiveLine Y))
    (ordinary : diagonalTracePush l (ProjectiveLine Y ↘ Y) ⋙ eY.F ≅
      eP.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
        (ProjectiveLine Y ↘ Y))
    (hordinary : ∀ M : DiagonalCompleted l (ProjectiveLine Y),
      HEq ((ordinary.hom.app M).hom ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map (eP.underlying.hom.app M))
        (eY.underlying.hom.app ((diagonalTracePush l (ProjectiveLine Y ↘ Y)).obj M))) :
    eY.F.map (DiagonalTrace.completedPushUnit l (ProjectiveLine Y ↘ Y)) ≫
        ordinary.hom.app _ ≫
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
            (ProjectiveLine Y ↘ Y)).map eP.unitIso.hom =
      eY.unitIso.hom ≫ coefficientOrdinaryUnit _ Y := by
  let UY := SheafOfModules.unit (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))
  let UP := SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
  let G := lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)
  let m := DiagonalTrace.completedPushUnit l (ProjectiveLine Y ↘ Y)
  let a := (SheafOfModules.toSheaf
    (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map m
  have ho := eq_of_heq (hordinary UP)
  have hn := eY.underlying.hom.naturality m
  have h : (eY.F.map m).hom ≫ (ordinary.hom.app UP).hom =
      eY.underlying.hom.app UY ≫ a ≫ G.map (eP.underlying.inv.app UP) := by
    apply (cancel_mono (G.map (eP.underlying.hom.app UP))).mp
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_app,
      G.map_id]
    rw [ho]
    exact hn
  apply (cancel_epi eY.unitIso.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply Mod.regular_hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom]
  rw [reassoc_of% h]
  have hY := unitRealization_inv_one l Y eY
  have hP := unitRealization_one l (ProjectiveLine Y) eP
  change η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y] ≫
    (eY.unitIso.inv.hom ≫ eY.underlying.hom.app UY) = _ at hY
  change η[(completedAbFunctor (ProjectiveLine Y)).obj
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)] ≫
    (eP.underlying.inv.app UP ≫ eP.unitIso.hom.hom) = _ at hP
  erw [reassoc_of% hY]
  erw [reassoc_of% completedPushUnit_one l (ProjectiveLine Y ↘ Y)]
  rw [coefficientOrdinaryUnit_underlying]
  have hc := (isMonHom_condensedPushforwardHom
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y ↘ Y)).one_hom
  erw [hc]
  change _ = Functor.LaxMonoidal.ε G ≫ G.map
    η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ Functor.LaxMonoidal.ε G ≫ G.map k) hP

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
