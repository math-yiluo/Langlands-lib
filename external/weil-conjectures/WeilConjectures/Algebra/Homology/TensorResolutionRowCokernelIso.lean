/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TensorBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Row cokernel of the tensor of two resolutions

Source: Stacks Project, Algebra, Tag 00M3, cokernel computation and functoriality.
(blueprint: lem-weil-pbc-tensor-resolution-row-cokernel-iso)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

private theorem row_tensor_square {R : Type u} [CommRing R]
    {X X' Y Y' M M' : ModuleCat.{u} R} (ε : X ⟶ M) (ε' : X' ⟶ M')
    (a : X ⟶ X') (b : Y ⟶ Y') (f : M ⟶ M') (ha : a ≫ ε' = ε ≫ f) :
    ((ε ⊗ₘ 𝟙 Y) ≫ (β_ M Y).hom) ≫
        ((b ⊗ₘ 𝟙 M) ≫ (𝟙 Y' ⊗ₘ f)) =
      (a ⊗ₘ b) ≫ (ε' ⊗ₘ 𝟙 Y') ≫ (β_ M' Y').hom := by
  rw [tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← BraidedCategory.braiding_naturality,
    ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ha]

private noncomputable def rowAugmentation {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).X 0 ⟶
      ((tensorRight M).mapHomologicalComplex (.down ℕ)).obj Q.complex where
  f q := (P.π.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom
  comm' q q' h := by
    simp only [  Functor.mapBifunctorHomologicalComplex_obj_obj_X_d,
    curriedTensor_obj_map, ← id_tensorHom,
      Functor.mapHomologicalComplex_obj_d, Functor.flip_obj_map, curriedTensor_map_app,
      ← tensorHom_id]
    rw [Category.assoc, ← BraidedCategory.braiding_naturality]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
    erw [Category.comp_id]

private theorem rowAugmentation_zero {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).d 1 0 ≫ rowAugmentation P Q = 0 := by
  ext q
  simp only [HomologicalComplex.comp_f, rowAugmentation, 
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f, curriedTensor_map_app, ← tensorHom_id,
    ← Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id, ProjectiveResolution.complex_d_comp_π_f_zero,
    HomologicalComplex.zero_f]
  simp

private noncomputable def rowDesc {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :=
  (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).descOpcycles
    (rowAugmentation P Q) 1 (by simp) (rowAugmentation_zero P Q)

private theorem rowDesc_isIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    IsIso (rowDesc P Q) := by
  rw [rowDesc, ChainComplex.isIso_descOpcycles_iff]
  constructor
  · apply HomologicalComplex.exact_of_degreewise_exact
    intro q
    let S := (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).map
      (tensorRight (Q.complex.X q))
    have hs : S.Exact := P.exact₀.map_of_epi_of_preservesCokernel
      (tensorRight (Q.complex.X q)) (inferInstance) (inferInstance)
    apply ShortComplex.exact_of_iso _ hs
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (β_ M (Q.complex.X q)) ?_ ?_
    · simp [S, ShortComplex.map]
    · simp [S, ShortComplex.map, rowAugmentation]
  · apply HomologicalComplex.epi_of_epi_f
    intro q
    change Epi ((P.π.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom)
    have : Epi (P.π.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) := by
      change Epi ((tensorRight (Q.complex.X q)).map (P.π.f 0))
      infer_instance
    infer_instance


/-- The row cokernel complex is the singly tensored resolution, naturally
with respect to augmentation-compatible maps of both resolutions.

Source: Stacks Project, Algebra, Tag 00M3, proof, cokernel computation and
functoriality paragraph.
(blueprint: lem-weil-pbc-tensor-resolution-row-cokernel-iso)

Proof: Tensor the cokernel cofork P₁ → P₀ → M with Q_q. Right exactness
of tensor makes the augmentation P₀ ⊗ Q_q → M ⊗ Q_q a cokernel of
P₁ ⊗ Q_q → P₀ ⊗ Q_q. Its comparison with the evaluated row cokernel
is an isomorphism. Compose it with the tensor braiding M ⊗ Q_q ≅ Q_q ⊗ M.
The differential square follows after precomposition with the cokernel
projection from tensor bifunctoriality and naturality of braiding, so these
maps assemble to a chain isomorphism. For compatible a and b, the square
before braiding follows from a₀ ≫ P'.π₀ = P.π₀ ≫ f after precomposing
with the row cokernel projection. Cancel that epimorphism and then apply
naturality of braiding to identify the resulting map with b ⊗ f. -/
theorem tensorResolutionRowCokernelIso (R : Type u) [CommRing R] :
    ∃ e : ∀ (M N : ModuleCat.{u} R) (P : ProjectiveResolution M)
        (Q : ProjectiveResolution N),
        (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).opcycles 0 ≅
          ((tensorRight M).mapHomologicalComplex (.down ℕ)).obj Q.complex,
      ∀ (M N M' N' : ModuleCat.{u} R)
        (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
        (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
        (f : M ⟶ M') (g : N ⟶ N')
        (a : P.complex ⟶ P'.complex) (b : Q.complex ⟶ Q'.complex)
        (_ha : a.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ f)
        (_hb : b.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ g),
        (e M N P Q).hom ≫ ChainComplex.tensorMap b f =
          HomologicalComplex.opcyclesMap
            ((CategoryTheory.Functor.uncurry.obj
      (CategoryTheory.Functor.mapBifunctorHomologicalComplex
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.down ℕ) (.down ℕ))).map
        (X := (P.complex, Q.complex)) (Y := (P'.complex, Q'.complex)) (a, b)) 0 ≫
              (e M' N' P' Q').hom := by
  have inst (M N : ModuleCat.{u} R) (P : ProjectiveResolution M)
      (Q : ProjectiveResolution N) : IsIso (rowDesc P Q) := rowDesc_isIso P Q
  refine ⟨fun M N P Q => asIso (rowDesc P Q), ?_⟩
  intro M N M' N' P Q P' Q' f g a b ha hb
  change rowDesc P Q ≫ ChainComplex.tensorMap b f =
    HomologicalComplex.opcyclesMap _ 0 ≫ rowDesc P' Q'
  rw [← CategoryTheory.cancel_epi
    ((((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).pOpcycles 0)]
  simp only [← Category.assoc, rowDesc, HomologicalComplex.p_descOpcycles]
  rw [HomologicalComplex.p_opcyclesMap, Category.assoc,
    HomologicalComplex.p_descOpcycles]
  ext q : 1
  simp only [HomologicalComplex.comp_f,  Functor.uncurry_obj_map,
    Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, curriedTensor_map_app,
    curriedTensor_obj_map, ← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp]
  change (((P.π.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom) ≫
    ((b.f q ⊗ₘ 𝟙 M) ≫ (𝟙 (Q'.complex.X q) ⊗ₘ f))) =
      (a.f 0 ⊗ₘ b.f q) ≫ (P'.π.f 0 ⊗ₘ 𝟙 (Q'.complex.X q)) ≫
        (β_ M' (Q'.complex.X q)).hom
  exact row_tensor_square (P.π.f 0) (P'.π.f 0) (a.f 0) (b.f q) f ha

end HomologicalComplex₂
