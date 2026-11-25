/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-! # Transport of pullback of sections along isomorphisms over a scheme

## References

* Stacks Project, Tags 0GJP and 0GJU, transport of the variety of vanishing cycles
* Stacks Project, Tag 0GJU, first paragraph and displayed fibre identification
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem iso_cancellation {C : Type*} [Category C]
    {A B D E F H : C} (a : A ≅ B) (l : D ≅ B) (j : D ≅ E)
    (c : F ≅ E) (d : F ≅ H) :
    j.hom ≫ c.inv ≫ d.hom =
      l.hom ≫ a.inv ≫ (a ≪≫ l.symm ≪≫ j ≪≫ c.symm ≪≫ d).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

set_option maxRecDepth 4096 in
/-- Pullback of global sections is unchanged under an isomorphism of its source and
its target over the coefficient scheme. There are no stalks, strict local schemes,
closed points or direct-image comparisons in this assertion. -/
theorem globalSections_iso_over_transport
    {X Y T L Z W V : Scheme.{u}}
    (p : Y ⟶ X) (h : T ⟶ Y) (ρ : L ⟶ Y)
    (w : W ⟶ T) (k : W ⟶ L) (hw : w ≫ h = k ≫ ρ)
    (g : Z ⟶ X) (v : V ⟶ Z) (q : L ≅ Z) (E : W ≅ V)
    (hq : q.hom ≫ g = ρ ≫ p) (hE : E.hom ≫ v = k ≫ q.hom)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ U : (Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} ρ).obj
          ((upperStar AddCommGrpCat.{u + 1} p).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G),
    ∃ B : (Sheaf.Γ W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} w).obj
          ((upperStar AddCommGrpCat.{u + 1} h).obj
            ((upperStar AddCommGrpCat.{u + 1} p).obj G))) ≅
      (Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} (v ≫ g)).obj G),
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} k
        ((upperStar AddCommGrpCat.{u + 1} ρ).obj
          ((upperStar AddCommGrpCat.{u + 1} p).obj G)) ≫
      (Sheaf.Γ W.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk hw)).hom.app
          ((upperStar AddCommGrpCat.{u + 1} p).obj G)) ≫ B.hom =
      U.hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} v
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) ≫
      (Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1} v g).inv.app G) := by
  let A := AddCommGrpCat.{u + 1}
  let K := (upperStar A p).obj G
  let P := (upperStar A g).obj G
  let ΓL := Sheaf.Γ L.smallEtaleTopology A
  let ΓW := Sheaf.Γ W.smallEtaleTopology A
  let ΓV := Sheaf.Γ V.smallEtaleTopology A
  let c := (squareUpperStarIso A (CommSq.mk hq)).app G
  let d := (squareUpperStarIso A (CommSq.mk hw)).app K
  let a := (upperStarComp A v g).app G
  let j := (upperStarComp A k q.hom).app P
  let l := (upperStarComp A E.hom v (k ≫ q.hom) hE.symm).app P
  let targetCoefficient :=
    (upperStar A E.hom).mapIso a ≪≫ l.symm ≪≫ j ≪≫
      (upperStar A k).mapIso c.symm ≪≫ d
  let U := (ΓL.mapIso c ≪≫ (globalSectionsUpperStarIso A q.hom P).symm)
  let B := (globalSectionsUpperStarIso A E.hom ((upperStar A (v ≫ g)).obj G) ≪≫
    ΓW.mapIso targetCoefficient).symm
  refine ⟨U, B, ?_⟩
  apply (cancel_epi U.inv).1
  apply (cancel_mono B.inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  change (globalSectionsUpperStarMap A q.hom P ≫ ΓL.map c.inv) ≫
      (globalSectionsUpperStarMap A k ((upperStar A ρ).obj K) ≫ ΓW.map d.hom) =
    (globalSectionsUpperStarMap A v P ≫ ΓV.map a.inv) ≫
      (globalSectionsUpperStarMap A E.hom ((upperStar A (v ≫ g)).obj G) ≫
        ΓW.map targetCoefficient.hom)
  have naturality {Y Z : Scheme.{u}} (m : Z ⟶ Y)
      {F F' : Sheaf Y.smallEtaleTopology A} (b : F ⟶ F') :
      (Sheaf.Γ Y.smallEtaleTopology A).map b ≫ globalSectionsUpperStarMap A m F' =
        globalSectionsUpperStarMap A m F ≫
          (Sheaf.Γ Z.smallEtaleTopology A).map ((upperStar A m).map b) := by
    let e := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A terminalIsTerminal
    have he (H : Sheaf Y.smallEtaleTopology A) : globalSectionsUpperStarMap A m H =
        (Sheaf.Γ Y.smallEtaleTopology A).map
          ((upperStarLowerStarAdjunction A m).unit.app H) ≫
        (lowerStarCompGlobalSectionsIso A m).hom.app _ := by
      change _ = _ ≫ e.hom.app _ ≫ _ ≫ _
      rw [e.hom.naturality_assoc]
      rfl
    rw [he, he]
    simp only [Category.assoc]
    rw [← (lowerStarCompGlobalSectionsIso A m).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    congr 1
    exact congrArg (Sheaf.Γ Y.smallEtaleTopology A).map
      ((upperStarLowerStarAdjunction A m).unit.naturality b)
  simp only [Category.assoc]
  rw [reassoc_of% (naturality k c.inv), reassoc_of% (naturality E.hom a.inv)]
  simp only [← Category.assoc]
  rw [← globalSectionsUpperStarMap_comp A k q.hom P]
  rw [← globalSectionsUpperStarMap_comp' A E.hom v (k ≫ q.hom) hE.symm P]
  have hc : j.hom ≫ (upperStar A k).map c.inv ≫ d.hom =
      l.hom ≫ (upperStar A E.hom).map a.inv ≫ targetCoefficient.hom := by
    exact iso_cancellation ((upperStar A E.hom).mapIso a) l j
      ((upperStar A k).mapIso c) d
  simp only [Category.assoc]
  change globalSectionsUpperStarMap A (k ≫ q.hom) P ≫
      ΓW.map j.hom ≫ ΓW.map ((upperStar A k).map c.inv) ≫ ΓW.map d.hom =
    globalSectionsUpperStarMap A (k ≫ q.hom) P ≫
      ΓW.map l.hom ≫ ΓW.map ((upperStar A E.hom).map a.inv) ≫
        ΓW.map targetCoefficient.hom
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun m ↦ globalSectionsUpperStarMap A (k ≫ q.hom) P ≫ ΓW.map m) hc

end AlgebraicGeometry.Etale
