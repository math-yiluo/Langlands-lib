/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!
# A linear retraction of `R ⟶ S` splits the unit of the extension of scalars

Let `C` be a braided monoidal category with coequalizers preserved by the tensor product,
`φ : R ⟶ S` a morphism of monoid objects with `R` commutative, and `ρ : S ⟶ R` an `R`-linear
retraction of `φ`: `φ ≫ ρ = 𝟙`, `ρ(φ(r) s) = r ρ(s)` and `ρ(s φ(r)) = ρ(s) r`. Then for every
`R`-module object `M`, the map `S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, is an `R`-linear retraction of
the unit `M ⟶ S ⊗_R M` of the adjunction `Mod.extendRestrictAdjunction φ`, naturally in `M`
(`Mod.extendScalarsRetraction`, `Mod.extendRestrictAdjunction_unit_comp_extendScalarsRetraction`).
In particular every component of this unit is a split monomorphism.

We also record that the three conditions on `ρ` are preserved by lax monoidal functors
(`Functor.LaxMonoidal.map_comp_mul_comp_retraction`), so that they can be checked on condensed
rings and transported to a scheme.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] (ρ : S ⟶ R)

/-- The map `S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, induced by a right `R`-linear map `ρ : S ⟶ R`, as
a morphism of `C`. -/
noncomputable def extendRetractionHom (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (M : Mod C R) :
    (extendScalarsObj φ M).X ⟶ M.X :=
  extendDescHom φ (ρ ▷ M.X ≫ γ[R,M.X]) (by
    rw [← comp_whiskerRight_assoc, Category.assoc, hr, comp_whiskerRight_assoc,
      Category.assoc, whisker_exchange_assoc, ModObj.mul_smul_self_flip,
      associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc])

@[reassoc (attr := simp)]
lemma extendπ_extendRetractionHom (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (M : Mod C R) :
    extendπ φ M ≫ extendRetractionHom φ ρ hr M = ρ ▷ M.X ≫ γ[R,M.X] :=
  extendπ_extendDescHom φ _ _

/-- The map `S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, induced by an `R`-linear map `ρ : S ⟶ R`, as a
morphism of `R`-module objects out of the restriction of scalars of `S ⊗_R M`. -/
noncomputable def extendRetraction (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R])
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (M : Mod C R) :
    (comap φ).obj (extendScalarsObj φ M) ⟶ M :=
  Hom.mk' (extendRetractionHom φ ρ hr M) (by
    change (φ ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X]) ≫
      extendRetractionHom φ ρ hr M = R ◁ extendRetractionHom φ ρ hr M ≫ γ[R,M.X]
    rw [← cancel_epi (R ◁ extendπ φ M), ← whiskerLeft_comp_assoc, extendπ_extendRetractionHom,
      Category.assoc, whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
      extendπ_extendRetractionHom, whiskerLeft_comp_assoc, ModObj.mul_smul_self_flip,
      associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc]
    simp only [← comp_whiskerRight_assoc, hl])

@[simp]
lemma extendRetraction_hom (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R])
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (M : Mod C R) :
    (extendRetraction φ ρ hl hr M).hom = extendRetractionHom φ ρ hr M :=
  rfl

/-- The retractions `S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, induced by an `R`-linear map `ρ : S ⟶ R`,
as a natural transformation `comap φ ∘ extendScalars φ ⟶ 𝟭`. -/
@[simps]
noncomputable def extendScalarsRetraction (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R])
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) :
    extendScalars φ ⋙ comap φ ⟶ 𝟭 (Mod C R) where
  app M := extendRetraction φ ρ hl hr M
  naturality M N f := hom_ext _ _ ((cancel_epi (extendπ φ M)).1 (by
    change extendπ φ M ≫ (extendScalarsMap φ f).hom ≫ extendRetractionHom φ ρ hr N =
      extendπ φ M ≫ extendRetractionHom φ ρ hr M ≫ f.hom
    rw [extendπ_extendScalarsMap_assoc, extendπ_extendRetractionHom,
      extendπ_extendRetractionHom_assoc, whisker_exchange_assoc, act_hom]))

/-- If `ρ : S ⟶ R` is an `R`-linear retraction of `φ : R ⟶ S`, then the maps
`S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, are retractions of the unit `M ⟶ S ⊗_R M`. -/
@[reassoc]
lemma extendRestrictAdjunction_unit_comp_extendScalarsRetraction (hρ : φ ≫ ρ = 𝟙 R)
    (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R]) (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) :
    (extendRestrictAdjunction φ).unit ≫ extendScalarsRetraction φ ρ hl hr = 𝟙 _ := by
  refine NatTrans.ext (funext fun M ↦ hom_ext _ _ ?_)
  change (extendUnitHom φ M ≫ 𝟙 _) ≫ extendRetractionHom φ ρ hr M = 𝟙 M.X
  rw [Category.comp_id, extendUnitHom, Category.assoc, Category.assoc, extendπ_extendRetractionHom,
    ← comp_whiskerRight_assoc, ← IsMonHom.one_hom φ, Category.assoc, hρ, Category.comp_id,
    ModObj.one_smul_self, Iso.inv_hom_id]

end CategoryTheory.Mod

namespace CategoryTheory.Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (G : C ⥤ D) [G.LaxMonoidal] {R S : C} [MonObj R] [MonObj S]

/-- A lax monoidal functor `G` preserves left linearity of a map `ρ : S ⟶ R` with respect to
`φ : R ⟶ S`: if `ρ(φ(r) s) = r ρ(s)`, then the same holds for `G φ` and `G ρ`. -/
lemma map_whiskerRight_comp_mul_comp_map (φ : R ⟶ S) (ρ : S ⟶ R)
    (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R]) :
    G.map φ ▷ G.obj S ≫ μ[G.obj S] ≫ G.map ρ = G.obj R ◁ G.map ρ ≫ μ[G.obj R] := by
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, μ_natural_left_assoc,
    μ_natural_right_assoc]
  simp only [← G.map_comp, hl]

/-- A lax monoidal functor `G` preserves right linearity of a map `ρ : S ⟶ R` with respect to
`φ : R ⟶ S`: if `ρ(s φ(r)) = ρ(s) r`, then the same holds for `G φ` and `G ρ`. -/
lemma map_whiskerLeft_comp_mul_comp_map (φ : R ⟶ S) (ρ : S ⟶ R)
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) :
    G.obj S ◁ G.map φ ≫ μ[G.obj S] ≫ G.map ρ = G.map ρ ▷ G.obj R ≫ μ[G.obj R] := by
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, μ_natural_right_assoc,
    μ_natural_left_assoc]
  simp only [← G.map_comp, hr]

end CategoryTheory.Functor.LaxMonoidal
