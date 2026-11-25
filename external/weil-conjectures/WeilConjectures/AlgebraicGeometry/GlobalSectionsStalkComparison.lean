/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Etale

private lemma eval_eq_res {C : Type u} [Category C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

/-- Pullback of a global section commutes with the inverse-image stalk comparison.
Source: Stacks Project, Tag 03Q1 (3), and the definition of globalSectionsUpperStarMap.
(blueprint: lemma-sheaves-finite-support-finite-morphisms--2).

Proof: Use inverseImage_stalk_germ with the identity étale neighbourhood of X.
The definition of globalSectionsUpperStarMap evaluates the adjunction unit there,
then restricts along the isomorphism from Y to the base change of X. The colimit
relation for toPresheafFiber identifies the germ after that restriction with the
induced germ in the base-change neighbourhood. Cancel the global-sections
identification and apply the germ compatibility from inverseImage_stalk_germ. -/
theorem exists_globalSections_stalk_comparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ c : (pointSmallEtale y).sheafFiber.obj (((g)^*[AddCommGrpCat.{u + 1}]).obj F) ≅
        (pointSmallEtale (y ≫ g)).sheafFiber.obj F,
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal @Etale Y)).hom.app
          (((g)^*[AddCommGrpCat.{u + 1}]).obj F) ≫
        (pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 Y))
          (Over.homMk y (Category.comp_id y))
          (((g)^*[AddCommGrpCat.{u + 1}]).obj F).obj ≫ c.hom =
      (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal @Etale X)).hom.app F ≫
        (pointSmallEtale (y ≫ g)).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
          (Over.homMk (y ≫ g) (Category.comp_id (y ≫ g))) F.obj := by
  -- Work at the chosen terminal object, then transport to the identity neighbourhoods.
  obtain ⟨c, hc⟩ := inverseImage_stalk_germ g y
  refine ⟨c.app F, ?_⟩
  let q : Scheme.Etale.mk (𝟙 X) ⟶ ⊤_ X.Etale := terminal.from _
  let r : Scheme.Etale.mk (𝟙 Y) ⟶ ⊤_ Y.Etale := terminal.from _
  let x := (pointSmallEtale (y ≫ g)).fiber.map q
    (Over.homMk (y ≫ g) (Category.comp_id (y ≫ g)))
  specialize hc F (⊤_ X.Etale) x
  -- Base change and the forgetful functor preserve terminal objects.
  have hp : (pointSmallEtale y).fiber.map (r ≫ (PreservesTerminal.iso g.Etale).inv)
      (Over.homMk y (Category.comp_id y)) =
      (pointSmallEtaleFiberEtaleIso g y).inv.app (⊤_ X.Etale) x := by
    have ht := (terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj
      (Scheme.Etale.forget Y)
    exact ht.hom_ext _ _
  let P := ((g)^*[AddCommGrpCat.{u + 1}]).obj F
  -- Cancel the chosen terminal evaluation before restricting to the identity object.
  have hY : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app P ≫
      P.ΓRes (op (Scheme.Etale.mk (𝟙 Y))) = P.obj.map r.op := by
    rw [← Sheaf.ΓRes_map P r.op, ← eval_eq_res _ _ terminalIsTerminal P]
    simp
  simp only [globalSectionsUpperStarMap, Category.assoc, eval_eq_res]
  rw [reassoc_of% hY]
  rw [← Category.assoc (P.obj.map _) (P.obj.map _), ← Functor.map_comp, ← op_comp]
  rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hp]
  erw [hc]
  rw [← Sheaf.ΓRes_map F q.op, Category.assoc,
    GrothendieckTopology.Point.toPresheafFiber_w]

end AlgebraicGeometry.Etale
