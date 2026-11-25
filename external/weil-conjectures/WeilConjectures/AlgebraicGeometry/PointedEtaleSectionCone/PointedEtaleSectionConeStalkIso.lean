/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionCone
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

/-! # Invertibility of restriction along a pointed section cone

## References

* Stacks Project, Tags 03Q9 and 03QO, the pointed germ comparison
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.PointedEtaleSectionCone

/-- Restriction along a pointed section cone is invertible whenever evaluation at a
compatible geometric point computes global sections of the pulled-back sheaf. -/
theorem isIso_restriction
    {S T : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {I : Type v} [Category.{v} I]
    {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}
    (c : PointedEtaleSectionCone g N)
    (y : Spec (.of Ω) ⟶ T) (hbase : y ≫ g = s)
    (hpoint : ∀ i : I, y ≫ (c.section_ i).left ≫
      pullback.fst (N.obj i).1.hom g = (N.obj i).2.left)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hγ : IsIso ((Scheme.pointSmallEtale y).toPresheafFiber
      (Scheme.Etale.mk (𝟙 T)) (Over.homMk y (Category.comp_id y))
      ((upperStar AddCommGrpCat.{v + 1} g).obj F).obj))
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F))
    (hr : c.IsRestriction F r) : IsIso r := by
  let P := (upperStar AddCommGrpCat.{v + 1} g).obj F
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{v + 1}
    (IsTerminal.isTerminalOfObj (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T)
      (Scheme.Etale.mk (𝟙 T)) Over.mkIdTerminal)
  let γ := (Scheme.pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
    (Over.homMk y (Category.comp_id y)) P.obj
  have : IsIso γ := hγ
  have comparison : ∀ (t : Spec (.of Ω) ⟶ S) (ht : y ≫ g = t),
      ∃ b : (Scheme.pointSmallEtale y).sheafFiber.obj P ≅
          (Scheme.pointSmallEtale t).sheafFiber.obj F,
        ∀ (U : S.Etale) (ū : (Scheme.pointSmallEtale t).fiber.obj U)
          (a : Scheme.Etale.mk (𝟙 T) ⟶ g.Etale.obj U),
          y ≫ a.left ≫ pullback.fst U.hom g = ū.left →
          ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app F).hom.app
            (op U) ≫ P.obj.map a.op ≫ γ ≫ b.hom =
            (Scheme.pointSmallEtale t).toPresheafFiber U ū F.obj := by
    intro t ht
    subst t
    obtain ⟨b, hb⟩ := inverseImage_stalk_germ g y
    refine ⟨b.app F, ?_⟩
    intro U ū a ha
    have hp : (Scheme.pointSmallEtale y).fiber.map a
        (Over.homMk y (Category.comp_id y)) =
        (Scheme.pointSmallEtaleFiberEtaleIso g y).inv.app U ū := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
        change (y ≫ a.left) ≫ pullback.fst U.hom g = ū.left
        exact ha
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
        change (y ≫ a.left) ≫ pullback.snd U.hom g = y
        rw [Category.assoc]
        have hw := a.w
        change a.left ≫ pullback.snd U.hom g = 𝟙 _ at hw
        rw [hw]
        rfl
    dsimp only [γ]
    rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hp]
    exact hb F U ū
  obtain ⟨b, hb⟩ := comparison s hbase
  let r₀ := b.inv ≫ inv γ ≫ e.inv.app P
  have hr₀ : c.IsRestriction F r₀ := by
    intro i
    have h := hb (N.obj i).1 (N.obj i).2 (c.section_ i) (hpoint i)
    change (Scheme.pointSmallEtale s).toPresheafFiber
      (N.obj i).1 (N.obj i).2 F.obj ≫ r₀ =
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app F).hom.app
          (op (N.obj i).1) ≫ P.obj.map (c.section_ i).op ≫ e.inv.app P
    dsimp only [r₀]
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
  have hEq : r = r₀ := (c.existsUnique_restriction F).unique hr hr₀
  rw [hEq]
  dsimp only [r₀]
  infer_instance

end AlgebraicGeometry.Etale.PointedEtaleSectionCone
