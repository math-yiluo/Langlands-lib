/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Constant-sheaf adjuncts and pullback

Source: Stacks Project, Tag 03F3; constant-sheaf and inverse-image adjunctions.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem constantSection_adjunct_restrict {Z : Scheme.{u}}
    (T T' : Z.Etale) (hT : IsTerminal T) (hT' : IsTerminal T') (f : T' ⟶ T)
    (M : AddCommGrpCat.{u + 1})
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶ G) :
    (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv M G m ≫
      G.obj.map f.op =
    (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1} hT').homEquiv M G m := by
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  have hn := (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M) ≫
    m.hom).naturality f.op
  change 𝟙 M ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn.symm

/-- The constant-sheaf adjunct of a pulled-back map is the adjunct followed by the
inverse-image unit, evaluated at the terminal pullback identification.
Source: Stacks Project, Tag 03F3, localization and restriction; the first step of
`lem-weil-pbc-etale-open-section-pullback`.
(blueprint: lem-weil-pbc-constant-section-adjunct-pullback)

Proof: Expand upperStarConstantSheafIso as leftAdjointUniq. Its inverse transports
homEquiv to the composite of the constant-sheaf and inverse-image adjunctions.
The ofNatIsoRight homEquiv formula inserts lowerStarCompSheafSectionsTerminalIso.
Expand the inverse-image homEquiv into its unit and the pushforward of the map.
Naturality of the unit moves the original map to the constant-sheaf adjunct.
The right-adjoint comparison evaluates a pushforward on the terminal fibre product,
then restricts along the unique map from the identity étale object into that product.
The map below is that unique map: its second projection is the identity. Finally
transport from the chosen categorical terminal objects to mk(id) by their unique
terminal isomorphisms; naturality of evaluation gives the displayed formula. This
argument needs no points or nonemptiness and applies to every coefficient object. -/
theorem constantSection_adjunct_pullback {X Y : Scheme.{u}} (i : Y ⟶ X)
    (M : AddCommGrpCat.{u + 1})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶ G) :
    let bX := Scheme.Etale.mk (𝟙 X)
    let bY := Scheme.Etale.mk (𝟙 Y)
    let t : bY ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj bX :=
      MorphismProperty.Over.homMk (pullback.lift i (𝟙 Y)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bX, bY])
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      (show IsTerminal bY from IsTerminal.ofUniqueHom
        (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
        (fun a f ↦ by
          apply MorphismProperty.Over.Hom.ext
          exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv M _
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).inv.app M ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} i).map m) =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (show IsTerminal bX from IsTerminal.ofUniqueHom
        (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
        (fun a f ↦ by
          apply MorphismProperty.Over.Hom.ext
          exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv M G m ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
        (op bX) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G).obj.map t.op := by
  dsimp only
  have hc :
      (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).homEquiv M _
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).inv.app M ≫
          (Etale.upperStar AddCommGrpCat.{u + 1} i).map m) =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).homEquiv M G m ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
        (op (⊤_ X.Etale)) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G).obj.map
        (PreservesTerminal.iso i.Etale).inv.op := by
    unfold Scheme.upperStarConstantSheafIso
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    change (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv M _
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _
        ((Etale.upperStar AddCommGrpCat.{u + 1} i).map m)) ≫ _ = _
    rw [(Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv_unit,
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit_naturality m,
      Adjunction.homEquiv_naturality_right]
    rfl
  let bX := Scheme.Etale.mk (𝟙 X)
  let bY := Scheme.Etale.mk (𝟙 Y)
  have hbX : IsTerminal bX := IsTerminal.ofUniqueHom
    (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
    (fun a f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  have hbY : IsTerminal bY := IsTerminal.ofUniqueHom
    (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
    (fun a f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let sX : bX ⟶ ⊤_ X.Etale := terminal.from bX
  let sY : bY ⟶ ⊤_ Y.Etale := terminal.from bY
  let t : bY ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj bX :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 Y)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bX, bY])
  have ht : sY ≫ (PreservesTerminal.iso i.Etale).inv =
      t ≫ i.Etale.map sX :=
    (terminalIsTerminal.isTerminalObj i.Etale).hom_ext _ _
  have hc' := congrArg (fun q ↦ q ≫
    ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G).obj.map sY.op) hc
  rw [constantSection_adjunct_restrict _ _ terminalIsTerminal hbY sY] at hc'
  simp only [Category.assoc] at hc'
  rw [← Functor.map_comp, ← op_comp, ht, op_comp, Functor.map_comp] at hc'
  have hn := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
    G).hom.naturality sX.op
  change G.obj.map sX.op ≫
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
      (op bX) =
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
      (op (⊤_ X.Etale)) ≫
    ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G).obj.map (i.Etale.map sX).op at hn
  rw [← reassoc_of% hn] at hc'
  rw [← Category.assoc, constantSection_adjunct_restrict _ _
    terminalIsTerminal hbX sX] at hc'
  exact hc'

end AlgebraicGeometry
