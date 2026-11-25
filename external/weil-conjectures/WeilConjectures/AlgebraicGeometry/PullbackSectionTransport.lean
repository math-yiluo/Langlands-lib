/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Changing coefficients on the intermediate scheme in pullback sections

Source: Stacks Project, Tags 03S2 and 00XZ, inverse-image composition and its unit.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Global sections transport along inverse-image composition and a specified sheaf
isomorphism on the intermediate scheme. 
(blueprint: lem-weil-pbc-pullback-section-transport)
-/
noncomputable def pullbackSectionTransportEquiv
    {X Y L : Scheme.{u}} (a : L ⟶ Y) (b : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : (upperStar AddCommGrpCat.{u + 1} b).obj G ≅ H) :
    (Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} (a ≫ b)).obj G) ≃+
    (Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} a).obj H) :=
  Iso.addCommGroupIsoToAddEquiv
    ((Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      ((upperStarComp AddCommGrpCat.{u + 1} a b).app G ≪≫
        (upperStar AddCommGrpCat.{u + 1} a).mapIso i))

set_option backward.isDefEq.respectTransparency false in
private theorem globalSectionsUpperStarMap_natural
    {L K : Scheme.{u}} (m : K ⟶ L)
    {F F' : Sheaf L.smallEtaleTopology AddCommGrpCat.{u + 1}} (k : F ⟶ F') :
    (Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).map k ≫
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} m F' =
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} m F ≫
      (Sheaf.Γ K.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStar AddCommGrpCat.{u + 1} m).map k) := by
  let A := AddCommGrpCat.{u + 1}
  let eL := Sheaf.ΓNatIsoSheafSections L.smallEtaleTopology A terminalIsTerminal
  let eK := Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology A terminalIsTerminal
  let adj := upperStarLowerStarAdjunction A m
  have hu := congrArg (fun φ ↦ φ.hom.app (op (⊤_ L.Etale))) (adj.unit.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [eL.hom.naturality_assoc k]
  change eL.hom.app F ≫ k.hom.app (op (⊤_ L.Etale)) ≫
      (adj.unit.app F').hom.app (op (⊤_ L.Etale)) ≫
      ((upperStar A m).obj F').obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ =
    eL.hom.app F ≫ (adj.unit.app F).hom.app (op (⊤_ L.Etale)) ≫
      ((upperStar A m).obj F).obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ ≫ (Sheaf.Γ K.smallEtaleTopology A).map ((upperStar A m).map k)
  rw [reassoc_of% hu]
  have hn := ((upperStar A m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  change ((upperStar A m).obj F).obj.map
      (PreservesTerminal.iso m.Etale).inv.op ≫
      ((upperStar A m).map k).hom.app (op (⊤_ K.Etale)) =
    ((lowerStar A m).map ((upperStar A m).map k)).hom.app
      (op (⊤_ L.Etale)) ≫
      ((upperStar A m).obj F').obj.map
        (PreservesTerminal.iso m.Etale).inv.op at hn
  rw [← reassoc_of% hn]
  have hk := eK.inv.naturality ((upperStar A m).map k)
  change ((upperStar A m).map k).hom.app (op (⊤_ K.Etale)) ≫ eK.inv.app _ =
    eK.inv.app _ ≫ (Sheaf.Γ K.smallEtaleTopology A).map ((upperStar A m).map k) at hk
  rw [hk]

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the sheaf on the intermediate scheme commutes with pullback of global
sections along a morphism over that scheme.

Source: Stacks Project, Tags 03S2 and 00XZ, functorial inverse image and its unit.
(blueprint: lem-weil-pbc-pullback-section-transport).

Proof: Expand transport as the global-sections functor applied to upperStarComp,
followed by upperStar applied to i. Naturality of the inverse-image adjunction unit,
evaluation at the terminal object and the terminal base-change isomorphism shows that
globalSectionsUpperStarMap is natural in its sheaf argument. Apply this to i and to
the composition comparison. Associativity coherence of upperStarComp for m, a, b
identifies the two resulting composition comparisons. The equality m ≫ a = c replaces
the intermediate composite by c. After applying the global-sections functor the two
composites are equal as additive homomorphisms, hence on every s. Only the indicated
triangle is needed; no other projection, coefficient finiteness, or nonemptiness is used. -/
theorem pullbackSectionTransportEquiv_naturality
    {X Y L K : Scheme.{u}} (a : L ⟶ Y) (c : K ⟶ Y) (b : Y ⟶ X)
    (m : K ⟶ L) (hm : m ≫ a = c)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : (upperStar AddCommGrpCat.{u + 1} b).obj G ≅ H)
    (s : (Sheaf.Γ L.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} (a ≫ b)).obj G)) :
    let A := AddCommGrpCat.{u + 1}
    pullbackSectionTransportEquiv c b G H i
      ((globalSectionsUpperStarMap A m ((upperStar A (a ≫ b)).obj G) ≫
        (Sheaf.Γ K.smallEtaleTopology A).map
          ((upperStarComp A m (a ≫ b) (c ≫ b)
            (by rw [← Category.assoc, hm])).inv.app G)) s) =
    (globalSectionsUpperStarMap A m ((upperStar A a).obj H) ≫
      (Sheaf.Γ K.smallEtaleTopology A).map
        ((upperStarComp A m a c hm.symm).inv.app H))
          (pullbackSectionTransportEquiv a b G H i s) := by
  subst c
  let A := AddCommGrpCat.{u + 1}
  let j := (upperStarComp A a b).hom.app G ≫ (upperStar A a).map i.hom
  have hc := congrArg (fun e ↦ e.hom.app G)
    (upperStarComp_assoc A m a b ((m ≫ a) ≫ b) (Category.assoc m a b))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hc
  have hi := (upperStarComp A m a).inv.naturality i.hom
  simp only [Functor.comp_map] at hi
  have key₀ :
      (upperStarComp A m (a ≫ b) ((m ≫ a) ≫ b) (Category.assoc m a b)).inv.app G ≫
        (upperStarComp A (m ≫ a) b).hom.app G =
      (upperStar A m).map ((upperStarComp A a b).hom.app G) ≫
        (upperStarComp A m a).inv.app ((upperStar A b).obj G) := by
    apply (cancel_epi
      ((upperStarComp A m (a ≫ b) ((m ≫ a) ≫ b) (Category.assoc m a b)).hom.app G)).1
    simp only [Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hc]
    rw [Iso.hom_inv_id_app, Category.comp_id]
  have key : (upperStarComp A m (a ≫ b) ((m ≫ a) ≫ b)
      (Category.assoc m a b)).inv.app G ≫
      ((upperStarComp A (m ≫ a) b).hom.app G ≫
        (upperStar A (m ≫ a)).map i.hom) =
      (upperStar A m).map j ≫ (upperStarComp A m a).inv.app H := by
    simp only [← Category.assoc]
    rw [key₀]
    simp only [Category.assoc]
    rw [← hi]
    simp only [j, Functor.map_comp, Category.assoc]
  have hn := globalSectionsUpperStarMap_natural m j
  change
    ((globalSectionsUpperStarMap A m ((upperStar A (a ≫ b)).obj G) ≫
      (Sheaf.Γ K.smallEtaleTopology A).map
        ((upperStarComp A m (a ≫ b) ((m ≫ a) ≫ b) (Category.assoc m a b)).inv.app G)) ≫
      (Sheaf.Γ K.smallEtaleTopology A).map
        ((upperStarComp A (m ≫ a) b).hom.app G ≫
          (upperStar A (m ≫ a)).map i.hom)) s =
    (((Sheaf.Γ L.smallEtaleTopology A).map j ≫
      globalSectionsUpperStarMap A m ((upperStar A a).obj H)) ≫
      (Sheaf.Γ K.smallEtaleTopology A).map
        ((upperStarComp A m a).inv.app H)) s
  rw [Category.assoc, ← Functor.map_comp, key, Functor.map_comp,
    ← Category.assoc, ← hn]

end AlgebraicGeometry.Etale
