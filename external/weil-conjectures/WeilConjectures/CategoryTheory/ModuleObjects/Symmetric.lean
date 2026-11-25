/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!

# The symmetric monoidal category of module objects

Let `C` be a symmetric monoidal category with coequalizers, such that tensoring on either side
preserves colimits, and let `R : C` be a commutative algebra object. The braiding
`β_{M,N} : M ⊗ N ⟶ N ⊗ M` of `C` descends to the relative tensor products and gives a symmetric
monoidal structure on `Mod C R` (`Mod.symmetricCategory`).

The descent (`Mod.braidingHomX`) and the `R`-linearity of the induced map
(`Mod.braidingHom`) use the symmetry of `C`: for a merely braided `C` the braiding does not
respect the relations defining `M ⊗_R N`. The hexagon identities are checked after
precomposition with the epimorphisms `tensorObjπ`, using the description of the associator of
`Mod C R` in terms of the associator of `C` (`Mod.tensorObjπ_associator_hom`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

instance (M N : Mod C R) (X : C) : Epi (tensorObjπ M N ▷ X) :=
  (tensorRight X).map_epi (tensorObjπ M N)

instance (M N : Mod C R) (X : C) : Epi (X ◁ tensorObjπ M N) :=
  (tensorLeft X).map_epi (tensorObjπ M N)

/-- The associator of the relative tensor product is induced by the associator of `C`. -/
@[reassoc]
lemma tensorObjπ_associator_hom (M N P : Mod C R) :
    tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P ≫ (α_ M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫ M.X ◁ tensorObjπ N P ≫ tensorObjπ M (N ⊗ P) := by
  change tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P ≫
    (Bimod.whiskerRight (toBimodTensorIso M N).hom ((toBimod R).obj P)).hom ≫
      (Bimod.AssociatorBimod.hom _ _ _) ≫
        (Bimod.whiskerLeft ((toBimod R).obj M) (toBimodTensorIso N P).inv).hom = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodTensorIso_hom_hom, id_whiskerRight, Category.id_comp]
  dsimp only [Bimod.AssociatorBimod.hom, Bimod.AssociatorBimod.homAux]
  erw [coequalizer.π_desc_assoc]
  slice_lhs 1 3 => erw [π_tensor_id_preserves_coequalizer_inv_desc]
  simp only [Category.assoc]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap]
  simp only [parallelPairHom_app_one]
  erw [toBimodTensorIso_inv_hom, whiskerLeft_id, Category.id_comp]
  rfl

/-- The inverse of the associator of the relative tensor product is induced by the inverse of the
associator of `C`. -/
@[reassoc]
lemma tensorObjπ_associator_inv (M N P : Mod C R) :
    M.X ◁ tensorObjπ N P ≫ tensorObjπ M (N ⊗ P) ≫ (α_ M N P).inv.hom =
      (α_ M.X N.X P.X).inv ≫ tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P := by
  have := tensorObjπ_associator_hom_assoc M N P (α_ M N P).inv.hom
  rw [← comp_hom', Iso.hom_inv_id, id_hom', Category.comp_id] at this
  rw [this, Iso.inv_hom_id_assoc]

@[reassoc]
lemma whiskerLeft_smul_tensorπ (M N : Mod C R) :
    M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      (α_ M.X R N.X).inv ≫ ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ tensorObjπ M N := by
  rw [tensorObjπ_condition, Category.assoc, Iso.inv_hom_id_assoc]

end CategoryTheory.Mod

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

@[reassoc]
lemma braiding_tensor_left_comp_whiskerLeft_braiding (M R N : C) :
    (β_ (M ⊗ R) N).hom ≫ N ◁ (β_ M R).hom ≫ (α_ N R M).inv ≫ (β_ N R).hom ▷ M =
      (α_ M R N).hom ≫ (β_ M (R ⊗ N)).hom := by
  rw [← cancel_mono ((β_ R N).hom ▷ M)]
  simp only [Category.assoc, ← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight,
    Category.comp_id]
  rw [← braiding_naturality_right, braiding_tensor_left_hom, braiding_tensor_right_hom]
  simp

@[reassoc]
lemma braiding_tensor_left_comp_braiding_whiskerRight (R M N : C) :
    (α_ R M N).inv ≫ (β_ (R ⊗ M) N).hom ≫ (α_ N R M).inv ≫ (β_ N R).hom ▷ M =
      R ◁ (β_ M N).hom ≫ (α_ R N M).inv := by
  rw [braiding_tensor_left_hom]
  simp [← comp_whiskerRight, SymmetricCategory.symmetry]

end CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [SymmetricCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- The braiding of `C` descends to the relative tensor product. -/
noncomputable def braidingHomX (M N : Mod C R) : (M ⊗ N).X ⟶ (N ⊗ M).X :=
  coequalizer.desc ((β_ M.X N.X).hom ≫ tensorObjπ N M) (by
    change ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ (β_ M.X N.X).hom ≫ tensorObjπ N M =
      ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ (β_ M.X N.X).hom ≫ tensorObjπ N M
    rw [comp_whiskerRight, Category.assoc, Category.assoc]
    erw [braiding_naturality_left_assoc, braiding_naturality_left_assoc, whiskerLeft_smul_tensorπ,
      braiding_naturality_right_assoc]
    rw [comp_whiskerRight, Category.assoc]
    erw [braiding_tensor_left_comp_whiskerLeft_braiding_assoc])

@[reassoc (attr := simp)]
lemma tensorObjπ_braidingHomX (M N : Mod C R) :
    tensorObjπ M N ≫ braidingHomX M N = (β_ M.X N.X).hom ≫ tensorObjπ N M :=
  coequalizer.π_desc _ _

/-- The braiding of `C` induces a morphism of `R`-modules `M ⊗_R N ⟶ N ⊗_R M`. -/
noncomputable def braidingHom (M N : Mod C R) : M ⊗ N ⟶ N ⊗ M :=
  Hom.mk' (braidingHomX M N) (by
    change γ[R,(M ⊗ N).X] ≫ braidingHomX M N = R ◁ braidingHomX M N ≫ γ[R,(N ⊗ M).X]
    rw [← cancel_epi (R ◁ tensorObjπ M N), whiskerLeft_tensorπ_smul_assoc, tensorObjπ_braidingHomX,
      ← whiskerLeft_comp_assoc, tensorObjπ_braidingHomX, whiskerLeft_comp_assoc,
      whiskerLeft_tensorπ_smul]
    erw [braiding_naturality_left_assoc, whiskerLeft_smul_tensorπ]
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    erw [braiding_tensor_left_comp_braiding_whiskerRight_assoc])

@[simp]
lemma braidingHom_hom (M N : Mod C R) : (braidingHom M N).hom = braidingHomX M N := rfl

@[reassoc (attr := simp)]
lemma braidingHom_braidingHom (M N : Mod C R) : braidingHom M N ≫ braidingHom N M = 𝟙 _ := by
  ext
  rw [← cancel_epi (tensorObjπ M N)]
  simp

@[reassoc (attr := simp)]
lemma tensorObjπ_whiskerRight_braidingHomX (M N : Mod C R) (X : C) :
    tensorObjπ M N ▷ X ≫ braidingHomX M N ▷ X = (β_ M.X N.X).hom ▷ X ≫ tensorObjπ N M ▷ X := by
  rw [← comp_whiskerRight, tensorObjπ_braidingHomX, comp_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerLeft_tensorπ_braidingHomX (M N : Mod C R) (X : C) :
    X ◁ tensorObjπ M N ≫ X ◁ braidingHomX M N = X ◁ (β_ M.X N.X).hom ≫ X ◁ tensorObjπ N M := by
  rw [← whiskerLeft_comp, tensorObjπ_braidingHomX, whiskerLeft_comp]

/-- The braiding of the relative tensor product, induced by the braiding of `C`. -/
@[simps]
noncomputable def braiding (M N : Mod C R) : M ⊗ N ≅ N ⊗ M where
  hom := braidingHom M N
  inv := braidingHom N M

set_option linter.flexible false in
/-- The relative tensor product over a commutative algebra object in a symmetric monoidal
category is braided. -/
noncomputable instance braidedCategory : BraidedCategory (Mod C R) where
  braiding := braiding
  braiding_naturality_right M {N P} f := by
    ext
    rw [← cancel_epi (tensorObjπ M N)]
    simp [tensorObjπ_whiskerLeft_assoc, tensorObjπ_whiskerRight]
  braiding_naturality_left {M N} f P := by
    ext
    rw [← cancel_epi (tensorObjπ M P)]
    simp [tensorObjπ_whiskerLeft, tensorObjπ_whiskerRight_assoc]
  hexagon_forward M N P := by
    ext
    rw [← cancel_epi (tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P)]
    simp [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerRight_assoc]
    erw [tensorObjπ_associator_hom, tensorObjπ_whiskerLeft]
    simp
  hexagon_reverse M N P := by
    ext
    rw [← cancel_epi (M.X ◁ tensorObjπ N P ≫ tensorObjπ M (N ⊗ P))]
    simp [tensorObjπ_associator_inv_assoc, tensorObjπ_whiskerLeft_assoc]
    erw [tensorObjπ_associator_inv, tensorObjπ_whiskerRight]
    simp

lemma braiding_hom_hom (M N : Mod C R) : (β_ M N).hom.hom = braidingHomX M N := rfl

/-- The relative tensor product over a commutative algebra object in a symmetric monoidal
category is symmetric. -/
noncomputable instance symmetricCategory : SymmetricCategory (Mod C R) where
  symmetry M N := braidingHom_braidingHom M N

end CategoryTheory.Mod
