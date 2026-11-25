/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitProjection
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # The balanced projection is the ordinary scalar adjunction transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.Mod

/-- The unit projection of the scalar extension–restriction adjunction for ordinary internal
modules is invertible.
Source: the balanced projection formula, Stacks 07A4.
Proof: braiding puts the restricted unit first. The resulting map is exactly the
balanced projectionHom followed by restriction of the left unitor, both
isomorphisms. This argument also applies to the zero ring.
(blueprint: lem-per-scalar-unit-projection-ordinary). -/
theorem isIso_unitProjection_extendRestrictAdjunction
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) :
    letI := comapLaxBraided φ
    IsIso ((extendRestrictAdjunction φ).unitProjection M) := by
  let := comapLaxBraided φ
  let F : Mod C R ⥤ Mod C S := extendScalars φ
  let U : Mod C S ⥤ Mod C R := comap φ
  let adj : F ⊣ U := extendRestrictAdjunction φ
  change IsIso (adj.unitProjection M)
  have he : adj.unitProjection M =
      (β_ M (U.obj (𝟙_ (Mod C S)))).hom ≫
        projectionHom φ (𝟙_ (Mod C S)) M ≫ U.map (λ_ (F.obj M)).hom := by
    dsimp only [projectionHom, Adjunction.unitProjection]
    rw [← extendRestrictAdjunction_unit_app]
    simp only [Category.assoc]
    change _ = (β_ M (U.obj (𝟙_ (Mod C S)))).hom ≫
      U.obj (𝟙_ (Mod C S)) ◁ adj.unit.app M ≫
        Functor.LaxMonoidal.μ U (𝟙_ (Mod C S)) (F.obj M) ≫ _
    erw [← BraidedCategory.braiding_naturality_left_assoc]
    dsimp only [Functor.comp_obj]
    erw [← Functor.LaxBraided.braided_assoc]
    rw [← U.map_comp]
    simp
  rw [he]
  infer_instance

end CategoryTheory.Mod
