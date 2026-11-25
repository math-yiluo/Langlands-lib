/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constant pullback composition coherence

Source: Stacks Project, sites.tex, Tag 03CB; cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-constant-pullback-composition-coherence)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Constant-sheaf comparison morphisms commute with inverse-image composition.
Source: Stacks Project, sites.tex, Tag 03CB (composition of inverse images), and
cohomology.tex, Tag 01F8, applied to the constant sheaf.

Proof: the constant-sheaf comparisons are the unique left-adjoint comparisons for
constant sheaf followed by inverse image, both left adjoint to global sections.
The comparison upperStarComp is obtained by conjugating the composition comparison
for direct images. That comparison on sections over the terminal object is the
canonical pullback-pasting identification. Thus both displayed maps have the same
adjoint, namely the identity of the constant coefficient object followed by the
adjunction unit for the composite. Uniqueness under the adjunction gives equality.
This is an equality of sheaf morphisms, before applying cohomology in any degree.
(blueprint: lem-weil-pbc-constant-pullback-composition-coherence)
-/
theorem constantPullbackCompositionCoherence {X Y Z : Scheme.{u}}
    (u : X ⟶ Y) (v : Y ⟶ Z) (M : AddCommGrpCat.{u + 1}) :
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (u ≫ v)).inv.app M) ≫
        (upperStarComp AddCommGrpCat.{u + 1} u v).hom.app
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} u).inv.app M ≫
        ((u)^*[AddCommGrpCat.{u + 1}]).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).inv.app M) := by
  have homEquiv_comparison
      {L L' : AddCommGrpCat.{u + 1} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      {R : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}}
      (adj : L ⊣ R) (adj' : L' ⊣ R)
      (A : AddCommGrpCat.{u + 1}) (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : L.obj A ⟶ B) :
      adj'.homEquiv A B ((Adjunction.leftAdjointUniq adj adj').inv.app A ≫ f) =
        adj.homEquiv A B f := by
    rw [Adjunction.leftAdjointUniq_inv_app, adj'.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, adj.homEquiv_apply]
  -- Compare the two morphisms under the constant-sheaf adjunction on X.
  apply (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv M _ |>.injective
  simp only [Scheme.upperStarConstantSheafIso]
  rw [homEquiv_comparison, homEquiv_comparison]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    Adjunction.comp_homEquiv]
  change (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv M _
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (u ≫ v)).homEquiv _ _ _) ≫ _ =
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv M _
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv _ _ _) ≫ _
  -- The composition unit law and naturality give the same successive units.
  rw [(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (u ≫ v)).homEquiv_apply,
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv_apply,
    upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} u v,
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit_naturality]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rw [Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.comp_unit_app]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app]
  simp only [Category.assoc]
  rw [Adjunction.homEquiv_apply]
  simp only [Category.assoc]
  rw [← (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} v).hom.naturality_assoc]
  congr 2
  simp only [Functor.comp_map]
  congr 1
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.symm_hom]
  -- The remaining section maps come from maps into the same terminal object.
  let F := ((u)^*[AddCommGrpCat.{u + 1}]).obj
    (((v)^*[AddCommGrpCat.{u + 1}]).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))
  change ((lowerStarComp AddCommGrpCat.{u + 1} u v).hom.app F).hom.app
    (Opposite.op (⊤_ Z.Etale)) ≫ _ = _
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    lowerStar, Functor.sheafPushforwardContinuous_obj_obj_map]
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [Iso.op_inv, Quiver.Hom.unop_op, unop_comp]
  exact (IsTerminal.isTerminalObj u.Etale _
    (IsTerminal.isTerminalObj v.Etale _ terminalIsTerminal)).hom_ext _ _

end AlgebraicGeometry.Etale
