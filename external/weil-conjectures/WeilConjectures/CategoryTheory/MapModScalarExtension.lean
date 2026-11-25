/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # Monoidal inverse image commutes with extension of scalars

Source: Stacks Project, Modules on Sites, Tag 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- A monoidal left adjoint intertwines extensions along a ring map and its image.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-pe-mapmod-scalar-extension).

Proof: lift the monoidal adjunction to module objects for each ring. Both composites
are left adjoint to the same restriction functor: the comparison for the right
adjoints is `mapModComapIso`, followed by the unit naturality square. Uniqueness of
left adjoints gives the claimed natural isomorphism. This argument includes zero
rings and identity scalar maps. -/
def mapModExtendScalarsIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type w} [Category.{z} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    Mod.extendScalars φ ⋙ F.mapMod S ≅
      F.mapMod R ⋙ Mod.extendScalars (F.map φ) := by
  have hunit : adj.unitAlgHom R ≫ G.map (F.map φ) = φ ≫ adj.unitAlgHom S := by
    exact (adj.unit.naturality φ).symm
  let e : Mod.comap (F.map φ) ⋙ (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((Mod.comapComp (adj.unitAlgHom R) (G.map (F.map φ))).symm ≪≫
          Mod.comapCongr hunit ≪≫
          Mod.comapComp φ (adj.unitAlgHom S)) ≪≫
      (Functor.associator _ _ _).symm
  let a := ((adj.mapModAdjunction R).comp
    (Mod.extendRestrictAdjunction (F.map φ))).ofNatIsoRight e
  exact ((Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)).leftAdjointUniq a

end CategoryTheory.Functor
