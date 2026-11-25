/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# Scalar matrices under `Functor.mapMod`

For a lax monoidal functor `F : C ⥤ D` and an algebra object `R`, the image under
`F.mapMod R` of the `R`-linear map `R ⟶ R` given by a scalar `b : 𝟙 ⟶ R` is the
`F R`-linear map given by the scalar `ε ≫ F.map b`
(`CategoryTheory.Functor.mapMod_map_regularLift`). For an additive `F`, the same holds
entrywise for matrices between finite free modules
(`CategoryTheory.Functor.mapMod_map_matrix`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open MonoidalCategory Limits
open scoped CategoryTheory.Obj

variable {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R]

/-- `F.mapMod R` sends multiplication by the scalar `b` to multiplication by `ε ≫ F.map b`. -/
lemma mapMod_map_regularLift (b : 𝟙_ C ⟶ R) :
    (F.mapMod R).map (Mod.regularLift (Mod.regular R) b) ≫ (F.mapModRegularIso R).hom =
      (F.mapModRegularIso R).hom ≫
        Mod.regularLift (Mod.regular (F.obj R)) (LaxMonoidal.ε F ≫ F.map b) := by
  apply Mod.regular_hom_ext
  change (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
      (F.map (Mod.regularLift (Mod.regular R) b).hom ≫ 𝟙 _) =
    (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫ (𝟙 _ ≫ _)
  simp only [Category.comp_id, Category.id_comp]
  rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
    ← Functor.map_comp, Mod.one_comp_regularLift]

section Additive

/-- `F.mapMod R` is additive when `F` is. -/
instance additive_mapMod [Preadditive C] [MonoidalPreadditive C] [Preadditive D]
    [MonoidalPreadditive D] [F.Additive] : (F.mapMod R).Additive where
  map_add := by
    intros
    ext
    exact F.map_add

variable [Abelian C] [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft R)]
  [Abelian D] [MonoidalPreadditive D] [PreservesFiniteColimits (tensorLeft (F.obj R))]
  [F.Additive]

/-- An additive lax monoidal functor sends `R^n` to `(F R)^n`. -/
noncomputable def mapModFiniteFreeIso (n : ℕ) :
    (F.mapMod R).obj (Mod.finiteFree R n) ≅ Mod.finiteFree (F.obj R) n :=
  (F.mapMod R).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ F.mapModRegularIso R)

omit [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft (F.obj R))] in
/-- An additive lax monoidal functor sends a matrix of scalars `b j k` to the matrix of
scalars `ε ≫ F.map (b j k)`. -/
lemma mapMod_map_matrix {m n : ℕ} (b : Fin m → Fin n → (𝟙_ C ⟶ R)) :
    (F.mapModFiniteFreeIso R m).inv ≫ (F.mapMod R).map
        (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular R) (b j k)) ≫
      (F.mapModFiniteFreeIso R n).hom =
    biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (F.obj R)) (LaxMonoidal.ε F ≫ F.map (b j k)) := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [mapModFiniteFreeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π, biproduct.matrix]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc, biproduct.lift_π]
  simp only [Category.assoc]
  rw [mapMod_map_regularLift, Iso.inv_hom_id_assoc]

end Additive

end CategoryTheory.Functor
