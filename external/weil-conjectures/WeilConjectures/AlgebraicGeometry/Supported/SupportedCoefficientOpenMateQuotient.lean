/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedLocalizationComparisons
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-!
# Normalization of the ordinary supported coefficient restriction mate

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, step 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

open Scheme

/-- The left mate of a right-adjoint restriction. This fixes the coefficient comparison
by the actual support restriction, including its normalization.
Source: Stacks Tag 09XP (blueprint: lem-pur-supported-coefficient-open-mate-quotient). -/
noncomputable def supportCoefficientMate
    {B : Type u₁} {C : Type u₂} {D : Type u₃}
    [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') :
    F' ⟶ F ⋙ H :=
  (Functor.leftUnitor F').inv ≫
    ((mateEquiv adj adj').symm
      (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r)))

private lemma constantUnit_terminal
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafAdj X.smallEtaleTopology C
      terminalIsTerminal).unit.app M ≫
      ((sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale))).map (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompSheafSectionsTerminalIso C i).hom.app _ =
    (constantSheafAdj Z.smallEtaleTopology C
      terminalIsTerminal).unit.app M := by
  let ax := constantSheafAdj X.smallEtaleTopology C terminalIsTerminal
  let az := constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal
  let p := upperStarLowerStarAdjunction C i
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ax.comp p).ofNatIsoRight e) az M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  change (ax.comp p).unit.app M ≫ e.hom.app _ ≫
    ((sheafSections Z.smallEtaleTopology C).obj
      (op (⊤_ Z.Etale))).map ((Scheme.upperStarConstantSheafIso
        C i).hom.app M) = az.unit.app M at h
  rw [← h]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← e.hom.naturality]
  rfl

private lemma constantUnit_global
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafΓAdj X.smallEtaleTopology C).unit.app M ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompGlobalSectionsIso C i).hom.app _ =
    (constantSheafΓAdj Z.smallEtaleTopology C).unit.app M := by
  let nx : Sheaf.Γ X.smallEtaleTopology C ≅
      (sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale)) := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology C terminalIsTerminal
  let nz : Sheaf.Γ Z.smallEtaleTopology C ≅
      (sheafSections Z.smallEtaleTopology C).obj
        (op (⊤_ Z.Etale)) := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology C terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have hx := (constantSheafΓAdj X.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj X.smallEtaleTopology C terminalIsTerminal) M
  have hz := (constantSheafΓAdj Z.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal) M
  have hinj : Function.Injective
      (fun f : M ⟶ (Sheaf.Γ Z.smallEtaleTopology C).obj
        ((constantSheaf Z.smallEtaleTopology C).obj M) ↦
        f ≫ nz.hom.app ((constantSheaf Z.smallEtaleTopology C).obj M)) :=
    fun f g h ↦ (cancel_mono _).1 h
  apply hinj
  simp only [nz, lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc]
  erw [nx.hom.naturality_assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]
  rw [← Category.assoc]
  erw [hx, hz]
  exact constantUnit_terminal C i M

private theorem globalSectionsUpperStarMap_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (m : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  let eL := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let eK := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m
  have hu := congrArg (fun φ ↦ φ.hom.app (Opposite.op (⊤_ Y.Etale))) (adj.unit.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [eL.hom.naturality_assoc k]
  change eL.hom.app F ≫ k.hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      (adj.unit.app F').hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ =
    eL.hom.app F ≫ (adj.unit.app F).hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k)
  rw [reassoc_of% hu]
  have hn := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  change ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map
      (PreservesTerminal.iso m.Etale).inv.op ≫
      ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app (Opposite.op (⊤_ X.Etale)) =
    ((lowerStar (ModuleCat.{u + 1} A) m).map ((upperStar (ModuleCat.{u + 1} A) m).map k)).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map
        (PreservesTerminal.iso m.Etale).inv.op at hn
  rw [← reassoc_of% hn]
  have hk := eK.inv.naturality ((upperStar (ModuleCat.{u + 1} A) m).map k)
  change ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app
    (Opposite.op (⊤_ X.Etale)) ≫ eK.inv.app _ =
    eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) at hk
  rw [hk]

end AlgebraicGeometry.Etale
