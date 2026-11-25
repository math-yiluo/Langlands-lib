/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-! # Restriction along compatible sections of an initial pointed étale diagram

The colimit universal property constructs restriction for any compatible family of
sections above an initial diagram of pointed neighbourhoods. No strict-local model
is built into this construction.

## References

* Stacks Project, Tag 03Q9, restriction from germs
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {S T : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
  {s : Spec (.of Ω) ⟶ S} {I : Type v} [Category.{v} I]
  {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}

/-- Compatible sections of the pullbacks of an initial pointed étale diagram. -/
structure PointedEtaleSectionCone (g : T ⟶ S)
    (N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements) where
  initial : N.Initial
  section_ (i : I) : Scheme.Etale.mk (𝟙 T) ⟶ g.Etale.obj (N.obj i).1
  naturality {i j : I} (a : i ⟶ j) :
    section_ i ≫ g.Etale.map
      ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).map (N.map a)) = section_ j

namespace PointedEtaleSectionCone

variable (c : PointedEtaleSectionCone g N)

/-- Restrict sections using the inverse-image unit and a section of the pullback. -/
noncomputable def restriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) (i : I) :
    F.obj.obj (op (N.obj i).1) ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app F).hom.app
      (op (N.obj i).1) ≫
    ((upperStar AddCommGrpCat.{v + 1} g).obj F).obj.map (c.section_ i).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T)
        (Scheme.Etale.mk (𝟙 T)) Over.mkIdTerminal)).inv.app _

/-- A stalk restriction is specified by all its pointed germ components. -/
def IsRestriction (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F)) : Prop :=
  ∀ i : I, (Scheme.pointSmallEtale s).toPresheafFiber (N.obj i).1 (N.obj i).2 F.obj ≫ r =
    c.restriction F i

/-- Compatible restrictions descend uniquely from the geometric stalk. -/
theorem existsUnique_restriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ∃! r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F), c.IsRestriction F r := by
  have : N.Initial := c.initial
  let k := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
  let hk : IsColimit k :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
  let d : Cocone (N.op ⋙ (Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙
      F.obj) :=
    { pt := (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F)
      ι := { app i := c.restriction F i.unop
             naturality := by
               intro i j a
               dsimp
               simp only [Category.comp_id, restriction]
               let t := (Functor.Elements.π (Scheme.pointSmallEtale s).fiber).map
                 (N.map a.unop)
               rw [← Category.assoc, ← Category.assoc]
               erw [((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app
                 F).hom.naturality t.op]
               simp only [Category.assoc]
               let H := (upperStar AddCommGrpCat.{v + 1} g).obj F
               change _ ≫ H.obj.map (g.Etale.map t).op ≫
                 H.obj.map (c.section_ j.unop).op ≫ _ = _
               rw [← H.obj.map_comp_assoc, ← op_comp, c.naturality a.unop]
               rfl } }
  refine ⟨hk.desc d, ?_, ?_⟩
  · intro i
    exact hk.fac d (op i)
  · intro r hr
    apply hk.hom_ext
    intro i
    exact (hr i.unop).trans (hk.fac d i).symm

end PointedEtaleSectionCone

end AlgebraicGeometry.Etale
