/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.InverseImageModule
import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The canonical inverse-image functor on modules

Source: Stacks Project, Sheaves, Tags 008X and 008Y.
(blueprint: lem-pc-inverse-image-module-functor-exact).
-/

@[expose] public section

universe u v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Limits TopologicalSpace

private theorem preservesColimitsOfShape_of_reflective
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U) [IsIso adj.counit]
    (H : D ⥤ E) (J : Type) [SmallCategory J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J L] [PreservesColimitsOfShape J (L ⋙ H)] :
    PreservesColimitsOfShape J H := by
  constructor
  intro K
  let e : (K ⋙ U) ⋙ L ≅ K :=
    Functor.isoWhiskerLeft K (asIso adj.counit) ≪≫ Functor.rightUnitor K
  have : PreservesColimit ((K ⋙ U) ⋙ L) H := by
    apply preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (K ⋙ U)))
    exact isColimitOfPreserves (L ⋙ H) (colimit.isColimit (K ⋙ U))
  exact preservesColimit_of_iso_diagram H e

namespace TopCat.Sheaf

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})

/-- The canonical inverse image on modules, with the specified maps.
Source: Stacks Project, Sheaves, Tags 008X and 008Y.
(blueprint: lem-pc-inverse-image-module-functor-exact). -/
def inverseImageModuleFunctor :
    SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
    SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (inverseImageRing f R)) where
  obj M := inverseImageModule f R M
  map a := inverseImageModuleMap f R _ a
  map_id M := by
    apply (SheafOfModules.toSheaf _).map_injective
    change (inverseImageConstruction f AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf _).map (𝟙 M)) = 𝟙 _
    simp
  map_comp a b := by
    apply (SheafOfModules.toSheaf _).map_injective
    change (inverseImageConstruction f AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf _).map (a ≫ b)) =
        (inverseImageConstruction f AddCommGrpCat.{u}).map
          ((SheafOfModules.toSheaf _).map a) ≫
        (inverseImageConstruction f AddCommGrpCat.{u}).map
          ((SheafOfModules.toSheaf _).map b)
    simp

/-- (blueprint: lem-pc-inverse-image-module-functor-exact) -/
instance inverseImageModuleFunctor_additive : (inverseImageModuleFunctor f R).Additive := by
  let G := (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have : G.Additive := ⟨by intros; rfl⟩
  have : (inverseImageConstruction f AddCommGrpCat.{u}).Additive :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{u} _ _).left_adjoint_additive
  constructor
  intro M N a b
  apply (SheafOfModules.toSheaf _).map_injective
  change (inverseImageConstruction f AddCommGrpCat.{u}).map
    ((SheafOfModules.toSheaf _).map (a + b)) =
      (inverseImageConstruction f AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf _).map a) +
      (inverseImageConstruction f AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf _).map b)
  simp

/-- (blueprint: lem-pc-inverse-image-module-functor-exact) -/
instance inverseImageModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImageModuleFunctor f R) := by
  let A := SheafOfModules.toSheaf ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (inverseImageRing f R))
  have : PreservesFiniteLimits (inverseImageConstruction f AddCommGrpCat.{u}) := by
    unfold inverseImageConstruction
    infer_instance
  have : PreservesFiniteLimits (inverseImageModuleFunctor f R ⋙ A) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf _ ⋙ inverseImageConstruction f AddCommGrpCat.{u})
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves (inverseImageModuleFunctor f R) A

private theorem toSheaf_preservesFiniteColimits
    {Z : TopCat.{u}} (S : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} S) := by
  constructor
  intro J _ _
  let L := PresheafOfModules.sheafification.{u} (𝟙 S.obj)
  have : PreservesFiniteColimits (L ⋙ SheafOfModules.toSheaf.{u} S) := by
    change PreservesFiniteColimits
      (PresheafOfModules.toPresheaf S.obj ⋙ presheafToSheaf _ AddCommGrpCat.{u})
    exact comp_preservesFiniteColimits _ _
  exact preservesColimitsOfShape_of_reflective
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj))
    (SheafOfModules.toSheaf.{u} S) J

/-- (blueprint: lem-pc-inverse-image-module-functor-exact) -/
instance inverseImageModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (inverseImageModuleFunctor f R) := by
  let A := SheafOfModules.toSheaf ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (inverseImageRing f R))
  have := toSheaf_preservesFiniteColimits
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have := toSheaf_preservesFiniteColimits
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (inverseImageRing f R))
  have : PreservesColimitsOfSize.{u, u}
      (inverseImageConstruction f AddCommGrpCat.{u}) :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{u} _ _).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (inverseImageModuleFunctor f R ⋙ A) := by
    change PreservesFiniteColimits
      (SheafOfModules.toSheaf _ ⋙ inverseImageConstruction f AddCommGrpCat.{u})
    exact comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_reflects_of_preserves (inverseImageModuleFunctor f R) A

/-- The canonical module inverse image is exact.
Source: Stacks Project, Sheaves, Tags 008X and 008Y.

Proof: its underlying abelian-sheaf functor is the explicit left Kan extension
followed by sheafification. The functor laws follow from the laws for that functor,
using faithfulness of the forgetful functor on modules. Additivity follows from
the abelian inverse-image adjunction, whose right adjoint is additive. The
underlying inverse image preserves finite limits by Mathlib's site pullback
construction; the module forgetful functor preserves and reflects finite limits.
For colimits, first observe that forgetting the module action commutes with module
sheafification. Sectionwise forgetting to abelian presheaves and abelian
sheafification both preserve colimits. Every diagram of sheaves of modules is
isomorphic, via the sheafification counit, to the sheafification of its underlying
presheaf diagram. Applying the preceding colimit preservation to this diagram
proves that forgetting to abelian sheaves preserves finite colimits. It reflects
them since it is conservative and preserves them. Abelian inverse image is a left
adjoint, so preserves colimits; the same argument now gives finite colimit
preservation for module inverse image. No stalk statement is used.
(blueprint: lem-pc-inverse-image-module-functor-exact). -/
theorem inverseImageModuleFunctor_exact :
    (inverseImageModuleFunctor f R).Additive ∧
      PreservesFiniteLimits (inverseImageModuleFunctor f R) ∧
        PreservesFiniteColimits (inverseImageModuleFunctor f R) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end
end TopCat.Sheaf
