/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-! # Transposition of the constant-sheaf pullback comparison

Source: Stacks Project, Tag 08J6; the constant-sheaf/global-sections adjunction.
-/

@[expose] public section

universe u v w v' w'
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

private lemma rightUniq_transpose
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    {F : C ⥤ D} {R R' : D ⥤ C} (a₁ : F ⊣ R) (a₂ : F ⊣ R')
    {M : C} {N : D} (f : F.obj M ⟶ N) :
    a₁.homEquiv M N f ≫ (a₁.rightAdjointUniq a₂).hom.app N = a₂.homEquiv M N f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (a₁.rightAdjointUniq a₂).hom.naturality f, ← Category.assoc,
    Adjunction.unit_rightAdjointUniq_hom_app]

private lemma leftUniq_transpose
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    {F F' : C ⥤ D} {R : D ⥤ C} (a₁ : F ⊣ R) (a₂ : F' ⊣ R)
    {M : C} {N : D} (f : F.obj M ⟶ N) :
    a₂.homEquiv M N ((a₁.leftAdjointUniq a₂).inv.app M ≫ f) =
      a₁.homEquiv M N f := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- The constant-sheaf comparison transposes inverse image to the unit on sections.
Source: Stacks Project, Tag 08J6 (remark-before-Leray), and Tag 01FA.
(blueprint: lem-weil-pbc-constant-sheaf-pullback-transpose)

Proof: The upperStarConstantSheafIso is the unique comparison between the two
left adjoints to sections on the source site. Its inverse therefore has identity
transpose for the composite adjunction. Transpose its composite with L(a):
naturality of the adjunction first gives the transpose of a followed by the
unit of L ⊣ g_*, and then the canonical identification of sections of g_* with
sections on the source. The Γ adjunction is transported from the terminal-section
adjunction using ΓNatIsoSheafSections. Substitution of the definition of
lowerStarCompGlobalSectionsIso cancels the two terminal-section identifications.
The remaining composite is precisely η.app F. This is an equality of group
homomorphisms before evaluation or passage to complexes. It holds for arbitrary
M and F, including zero objects and empty schemes. -/
theorem constantSheaf_pullback_transpose {X X' : Scheme.{u}} (g : X' ⟶ X)
    (M : AddCommGrpCat.{u + 1})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶ F) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g
    let η : Γ ⟶ L ⋙ Γ' :=
      (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom
    (constantSheafΓAdj X'.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv M (L.obj F)
        ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app M ≫ L.map a) =
      (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv M F a ≫
        η.app F := by
  let aX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let aY := constantSheafAdj X'.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let e := lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g
  have h := leftUniq_transpose ((aX.comp adj).ofNatIsoRight e) aY
    ((upperStar AddCommGrpCat.{u + 1} g).map a)
  dsimp only [upperStarConstantSheafIso] at ⊢
  apply (cancel_mono
    ((Sheaf.ΓNatIsoSheafSections X'.smallEtaleTopology
      AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app _)).mp
  dsimp only [Sheaf.ΓNatIsoSheafSections]
  rw [rightUniq_transpose]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  change aY.homEquiv M _ _ =
    aX.homEquiv M _ (adj.homEquiv _ _ ((upperStar AddCommGrpCat.{u + 1} g).map a)) ≫
      e.hom.app _ at h
  have hn := adj.unit.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Adjunction.homEquiv_unit adj, ← hn] at h
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    Sheaf.ΓNatIsoSheafSections, Iso.inv_hom_id_app]
  rw [← Category.assoc, ← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj]
  rw [rightUniq_transpose (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}) aX]
  exact h

end AlgebraicGeometry
