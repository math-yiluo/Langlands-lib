/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Pullbacks of constant sheaves and composition

The identifications `f^* A_Y ≅ A_X` of the pullbacks of constant sheaves with constant sheaves
(`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`) are compatible with the composition
isomorphisms of pullbacks (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)

/-- The unit of `Adjunction.ofNatIsoRight`. -/
private lemma ofNatIsoRight_unit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

omit [HasSmallSiteSheafify A] in
/-- The identification `f^* A_T ≅ A_S` through the units of the adjunctions. -/
private lemma unit_app_upperStarConstantSheafIso {S T : Scheme.{u}} (f : S ⟶ T) (a : A) :
    (constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology A).obj (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction A f).unit.app _ ≫
          (f)_*[A].map ((upperStarConstantSheafIso A f).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso A f).hom.app _ =
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).comp
        (upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso A f))
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app] at this
  rw [← this, upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso A f).hom.naturality]
  rfl

set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The identifications of global sections of pushforwards are compatible with composition. -/
private lemma lowerStarComp_hom_app_sheafSections (F : Sheaf X.smallEtaleTopology A) :
    ((sheafSections Z.smallEtaleTopology A).obj (op (⊤_ Z.Etale))).map
        ((lowerStarComp A g h).hom.app F) ≫
      (lowerStarCompSheafSectionsTerminalIso A (g ≫ h)).hom.app F =
    (lowerStarCompSheafSectionsTerminalIso A h).hom.app ((g)_*[A].obj F) ≫
      (lowerStarCompSheafSectionsTerminalIso A g).hom.app F := by
  simp [lowerStarCompSheafSectionsTerminalIso, lowerStarComp,
    Functor.sheafPushforwardContinuousComp']
  erw [Category.id_comp, ← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Quiver.Hom.unop_inj ((terminalIsTerminal.ofIso
    ((Hom.Etale g).mapIso (PreservesTerminal.iso (Hom.Etale h)) ≪≫
      PreservesTerminal.iso (Hom.Etale g)).symm).hom_ext _ _))

/-- The identifications `f^* A_Y ≅ A_X` are compatible with composition: the identification for
`g ≫ h` is `(g ≫ h)^* A_Z ≅ g^* h^* A_Z ≅ g^* A_Y ≅ A_X`.
(blueprint: `lem-weil-pbc-constant-pullback-composition-coherence`) -/
lemma upperStarConstantSheafIso_comp (a : A) :
    (upperStarComp A g h).hom.app ((constantSheaf Z.smallEtaleTopology A).obj a) ≫
        (g)^*[A].map ((upperStarConstantSheafIso A h).hom.app a) ≫
          (upperStarConstantSheafIso A g).hom.app a =
      (upperStarConstantSheafIso A (g ≫ h)).hom.app a := by
  have h1 : (upperStarLowerStarAdjunction A (g ≫ h)).unit.app
        ((constantSheaf Z.smallEtaleTopology A).obj a) ≫
      (g ≫ h)_*[A].map ((upperStarComp A g h).hom.app _ ≫
        (g)^*[A].map ((upperStarConstantSheafIso A h).hom.app a) ≫
          (upperStarConstantSheafIso A g).hom.app a) =
      ((upperStarLowerStarAdjunction A h).unit.app _ ≫
        (h)_*[A].map ((upperStarConstantSheafIso A h).hom.app a)) ≫
        (h)_*[A].map ((upperStarLowerStarAdjunction A g).unit.app _ ≫
            (g)_*[A].map ((upperStarConstantSheafIso A g).hom.app a)) ≫
          (lowerStarComp A g h).hom.app _ := by
    rw [Functor.map_comp, reassoc_of% (upperStarComp_hom_app_unit_app A g h
      ((constantSheaf Z.smallEtaleTopology A).obj a)), ← (lowerStarComp A g h).hom.naturality]
    have hn := (upperStarLowerStarAdjunction A g).unit.naturality
      ((upperStarConstantSheafIso A h).hom.app a)
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc] at hn ⊢
    simp only [← Functor.map_comp_assoc (h)_*[A]]
    rw [← reassoc_of% hn]
    rfl
  apply ((((constantSheafAdj Z.smallEtaleTopology A terminalIsTerminal).comp
    (upperStarLowerStarAdjunction A (g ≫ h))).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso A (g ≫ h))).homEquiv _ _).injective
  conv_rhs => rw [upperStarConstantSheafIso, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app, Adjunction.comp_unit_app]
  simp only [Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso A (g ≫ h)).hom.naturality]
  rw [Functor.comp_map, ← Functor.map_comp_assoc, h1]
  simp only [Functor.map_comp, Category.assoc]
  rw [lowerStarComp_hom_app_sheafSections]
  have hn := (lowerStarCompSheafSectionsTerminalIso A h).hom.naturality
    ((upperStarLowerStarAdjunction A g).unit.app ((constantSheaf Y.smallEtaleTopology A).obj a) ≫
      (g)_*[A].map ((upperStarConstantSheafIso A g).hom.app a))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]
  rw [← unit_app_upperStarConstantSheafIso A g a, ← unit_app_upperStarConstantSheafIso A h a]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
