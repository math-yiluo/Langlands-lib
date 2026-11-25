/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import all WeilConjectures.AlgebraicGeometry.IntegralSectionCoefficientNaturality
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # Pulling back a constant chart of the condensed coefficient ring

Source: Stacks Project, Tags 00YV and 03D2, and cartesian condensed coefficients.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private noncomputable def coefficientSiteSheafEquivalence (X : Scheme.{u})
    (D : Type*) [Category* D] :
    Sheaf (Scheme.ProEt.topology X) D ≌
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) D := by
  let : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).inducedTopology
          (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  exact Equivalence.sheafCongr (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) D

private noncomputable def constantComparison
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify K CommRingCat.{u + 1}]
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J CommRingCat.{u + 1} ⥤ Sheaf K CommRingCat.{u + 1})
    (adj : L ⊣ G.sheafPushforwardContinuous CommRingCat.{u + 1} J K)
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T)) :
    constantSheaf J CommRingCat.{u + 1} ⋙ L ≅ constantSheaf K CommRingCat.{u + 1} :=
  ((constantSheafAdj J CommRingCat.{u + 1} hT).comp adj).leftAdjointUniq
    (constantSheafAdj K CommRingCat.{u + 1} hGT)

private theorem constantComparison_unit
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify K CommRingCat.{u + 1}]
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J CommRingCat.{u + 1} ⥤ Sheaf K CommRingCat.{u + 1})
    (adj : L ⊣ G.sheafPushforwardContinuous CommRingCat.{u + 1} J K)
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))
    (k : Type (u + 1)) [CommRing k] (V : Cᵒᵖ) (a : k) :
    (((adj.homEquiv _ _)
      ((constantComparison J K G L adj hT hGT).app (CommRingCat.of k)).hom).hom.app V).hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app V a) =
      (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).app (G.op.obj V) a := by
  let b := (constantSheafAdj J CommRingCat.{u + 1} hT).comp adj
  let e := (constantComparison J K G L adj hT hGT).app (CommRingCat.of k)
  let ψ := (adj.homEquiv _ _) e.hom
  have h := b.unit_leftAdjointUniq_hom_app
    (constantSheafAdj K CommRingCat.{u + 1} hGT) (CommRingCat.of k)
  have ht := ConcreteCategory.congr_hom h a
  change (ψ.hom.app (op T)).hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a) =
    (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).app (op (G.obj T)) a at ht
  let q : op T ⟶ V := (hT.from V.unop).op
  have hJ := ConcreteCategory.congr_hom
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).naturality q) a
  have hK := ConcreteCategory.congr_hom
    ((toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).naturality (G.op.map q)) a
  change (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app V a =
    (((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map q).hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a) at hJ
  change (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).app (G.op.obj V) a =
    (((constantSheaf K CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map (G.op.map q)).hom
      ((toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).app (op (G.obj T)) a) at hK
  have hn := ConcreteCategory.congr_hom (ψ.hom.naturality q)
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a)
  change (ψ.hom.app V).hom
      ((((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map q).hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a)) = _ at hn
  change (ψ.hom.app V).hom
      ((((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map q).hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a)) =
    (((constantSheaf K CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map (G.op.map q)).hom
      ((ψ.hom.app (op T)).hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k))).app (op T) a)) at hn
  rw [← hJ] at hn
  exact hn.trans ((congrArg (fun x ↦
    (((G.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
      ((constantSheaf K CommRingCat.{u + 1}).obj (CommRingCat.of k))).obj.map q).hom x)
        ht).trans hK.symm)

/-- A constant chart of the reconstructed coefficient ring propagates along every scheme map.
Only coefficient rings occur in this assertion, with no input module or slice.

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tag 03D2.
(auxiliary; not a blueprint node).

Proof: transport c to the original sites using AsSmall. The cartesian coefficient
isomorphism identifies the inverse image of the internal ring on X with the internal
ring on Y. Section reconstruction identifies this with algebraic inverse image of its
section ring: the underlying set inverse image preserves the graphs of addition,
multiplication, zero and one. Inverse image of the constant k-ring is the constant k-ring,
by composing the constant-sheaf adjunction with the geometric adjunction. Pull back c
and compose these two identifications, then transport back by AsSmall to obtain d.
The unit equation of the ring inverse-image adjunction identifies its adjunct with
InternalModuleOperations.coefficientMap. Evaluating this equation on a constant scalar
a at each V gives the displayed equality. This argument works also for the empty scheme
and the zero ring: all maps used are natural ring isomorphisms.
-/
theorem exists_constant_coefficient_chart_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    ∃ d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
        smallRing Y (condensedRingObj Λ Y),
      ∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
        ((InternalModuleOperations.coefficientMap Λ f).hom.app (AsSmall.down.op.obj V)).hom
            ((c.hom.hom.app V).hom
              ((SheafOfModules.constantCoefficientUnit
                (Scheme.coefficientProEtaleModelTopology.{u, u} X) k).app V a)) =
          (d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)).hom
            ((SheafOfModules.constantCoefficientUnit
              (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k).app
                ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let K := Scheme.ProEt.topology Y
  let H := Scheme.coefficientProEtaleModelTopology.{u, u} Y
  let eX := coefficientSiteSheafEquivalence X CommRingCat.{u + 1}
  let eY := coefficientSiteSheafEquivalence Y CommRingCat.{u + 1}
  let G : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ Y.ProEt :=
    AsSmall.down ⋙ Scheme.proEtaleBaseChange f
  have : G.IsContinuous J K := Functor.isContinuous_comp AsSmall.down (Scheme.proEtaleBaseChange f)
    J (Scheme.ProEt.topology X) K
  let L := eX.inverse ⋙ Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let adj : L ⊣ G.sheafPushforwardContinuous CommRingCat.{u + 1} J K :=
    eX.symm.toAdjunction.comp (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})
  let T := AsSmall.up.obj (Scheme.ProEt.mk (𝟙 X))
  have hT : IsTerminal T := (Scheme.ProEt.isTerminalMkId X).isTerminalObj
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor _
  have hGT : IsTerminal (G.obj T) := (Scheme.ProEt.isTerminalMkId X).isTerminalObj
    (Scheme.proEtaleBaseChange f) _
  let a := (constantComparison J K G L adj hT hGT).app (CommRingCat.of k)
  let upY : Y.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} Y := AsSmall.up
  have : upY.IsContinuous K H := inferInstanceAs
    ((AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsContinuous K
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.inducedTopology K))
  let ty := Scheme.ProEt.isTerminalMkId Y
  have hty : IsTerminal (upY.obj (Scheme.ProEt.mk (𝟙 Y))) :=
    ty.isTerminalObj (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor _
  let b := (constantComparison K H upY eY.functor eY.toAdjunction ty hty).app
    (CommRingCat.of k)
  obtain ⟨r, hr⟩ := reconstructedCoefficientPullback Λ f
  let dO := a.symm ≪≫ L.mapIso c ≪≫ r
  let d := b.symm ≪≫ eY.functor.mapIso dO
  refine ⟨d, ?_⟩
  intro V z
  let VY := (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V
  have ha := constantComparison_unit J K G L adj hT hGT k V z
  have hb := constantComparison_unit K H upY eY.functor eY.toAdjunction ty hty k
    (AsSmall.down.op.obj VY) z
  have hc : c.hom ≫ (adj.homEquiv _ _) r.hom =
      (adj.homEquiv _ _) a.hom ≫
        (G.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map dO.hom := by
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    congr 1
    dsimp only [dO, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Iso.hom_inv_id_assoc]
  have hc' := congrArg (fun t ↦ (t.hom.app V).hom
    ((SheafOfModules.constantCoefficientUnit J k).app V z)) hc
  have hr' := congrArg (fun t ↦ (t.hom.app (AsSmall.down.op.obj V)).hom
    ((c.hom.hom.app V).hom ((SheafOfModules.constantCoefficientUnit J k).app V z))) hr
  have hb' : (b.hom.hom.app VY).hom
      ((toSheafify K ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))).app
        (AsSmall.down.op.obj VY) z) =
    (SheafOfModules.constantCoefficientUnit H k).app VY z := by
    change (b.hom.hom.app VY).hom
      ((((constantSheaf K CommRingCat.{u + 1}).obj (CommRingCat.of k)).obj.map
        (𝟙 (AsSmall.down.op.obj VY))).hom
          ((toSheafify K ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))).app
            (AsSmall.down.op.obj VY) z)) =
      (SheafOfModules.constantCoefficientUnit H k).app VY z at hb
    simpa using hb
  have hbInv : (b.inv.hom.app VY).hom
      ((SheafOfModules.constantCoefficientUnit H k).app VY z) =
    (toSheafify K ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))).app
      (AsSmall.down.op.obj VY) z := by
    rw [← hb']
    exact congrArg (fun t ↦ t.hom.app VY
      ((toSheafify K ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))).app
        (AsSmall.down.op.obj VY) z)) b.hom_inv_id
  change _ = (dO.hom.hom.app (AsSmall.down.op.obj VY)).hom
    ((b.inv.hom.app VY).hom ((SheafOfModules.constantCoefficientUnit H k).app VY z))
  rw [hbInv]
  change _ = (dO.hom.hom.app (G.op.obj V)).hom
    ((toSheafify K ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))).app (G.op.obj V) z)
  rw [← ha]
  have hc'' :
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _ r.hom).hom.app
          (AsSmall.down.op.obj V)
          ((c.hom.hom.app V).hom ((SheafOfModules.constantCoefficientUnit J k).app V z)) =
        (dO.hom.hom.app (G.op.obj V)).hom
          (((adj.homEquiv _ _) a.hom).hom.app V
            ((SheafOfModules.constantCoefficientUnit J k).app V z)) := by
    change
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _ r.hom).hom.app
          (AsSmall.down.op.obj V)).hom
          (((smallRing X (condensedRingObj Λ X)).obj.map (𝟙 V)).hom
            ((c.hom.hom.app V).hom ((SheafOfModules.constantCoefficientUnit J k).app V z))) =
        (dO.hom.hom.app (G.op.obj V)).hom
          (((adj.homEquiv _ _) a.hom).hom.app V
            ((SheafOfModules.constantCoefficientUnit J k).app V z)) at hc'
    rw [(smallRing X (condensedRingObj Λ X)).obj.map_id V] at hc'
    exact hc'
  exact hr'.symm.trans hc''

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
