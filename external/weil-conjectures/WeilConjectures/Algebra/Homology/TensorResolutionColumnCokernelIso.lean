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

/-!
# Column cokernel of the tensor of two resolutions

Source: Stacks Project, Algebra, Tag 00M3, cokernel computation and functoriality.
(blueprint: lem-weil-pbc-tensor-resolution-column-cokernel-iso)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

private def columnAugmentation {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).flip.X 0 ⟶
      ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex where
  f p := 𝟙 (P.complex.X p) ⊗ₘ Q.π.f 0
  comm' p p' h := by
    simp only [  flip_X_d, Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    curriedTensor_map_app, ← tensorHom_id,
      Functor.mapHomologicalComplex_obj_d, Functor.flip_obj_map, curriedTensor_map_app,
      ← tensorHom_id,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem columnAugmentation_zero {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).flip.d 1 0 ≫
      columnAugmentation P Q = 0 := by
  ext p
  simp only [HomologicalComplex.comp_f, columnAugmentation, flip_d_f,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d, curriedTensor_obj_map,
    ← id_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, ProjectiveResolution.complex_d_comp_π_f_zero,
    HomologicalComplex.zero_f]
  simp

private noncomputable def columnDesc {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :=
  (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).flip.descOpcycles
    (columnAugmentation P Q) 1 (by simp) (columnAugmentation_zero P Q)

private theorem columnDesc_isIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    IsIso (columnDesc P Q) := by
  rw [columnDesc, ChainComplex.isIso_descOpcycles_iff]
  constructor
  · apply HomologicalComplex.exact_of_degreewise_exact
    intro p
    simpa [ShortComplex.map, columnAugmentation, 
      curriedTensor_obj_map, ← id_tensorHom] using
      Q.exact₀.map_of_epi_of_preservesCokernel (tensorLeft (P.complex.X p))
        (inferInstance) (inferInstance)
  · apply HomologicalComplex.epi_of_epi_f
    intro p
    change Epi ((tensorLeft (P.complex.X p)).map (Q.π.f 0))
    infer_instance


/-- The column cokernel complex is the singly tensored resolution, naturally
with respect to augmentation-compatible maps of both resolutions.

Source: Stacks Project, Algebra, Tag 00M3, proof, cokernel computation and
functoriality paragraph.
(blueprint: lem-weil-pbc-tensor-resolution-column-cokernel-iso)

Proof: Tensor the cokernel cofork Q₁ → Q₀ → N with Pₚ. Tensoring is a left
adjoint, so the resulting cofork is a cokernel cofork. The evaluated column
cokernel of the bicomplex is another cokernel of the same map. Their unique
comparison is therefore an isomorphism. These comparisons commute with the
P differentials: precompose with the cokernel projection and use bifunctoriality
of tensor. They assemble to a chain isomorphism. For a and b compatible with
f and g, precomposing the naturality square with each cokernel projection
reduces it to b₀ ≫ Q'.π₀ = Q.π₀ ≫ g and tensor bifunctoriality.
Cancel the projections, which are epimorphisms, to obtain the stated square. -/
theorem tensorResolutionColumnCokernelIso (R : Type u) [CommRing R] :
    ∃ e : ∀ (M N : ModuleCat.{u} R) (P : ProjectiveResolution M)
        (Q : ProjectiveResolution N),
        (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).flip.opcycles 0 ≅
          ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex,
      ∀ (M N M' N' : ModuleCat.{u} R)
        (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
        (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
        (f : M ⟶ M') (g : N ⟶ N')
        (a : P.complex ⟶ P'.complex) (b : Q.complex ⟶ Q'.complex)
        (_ha : a.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ f)
        (_hb : b.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ g),
        (e M N P Q).hom ≫ ChainComplex.tensorMap a g =
          HomologicalComplex.opcyclesMap
            ((flipFunctor (ModuleCat R) (.down ℕ) (.down ℕ)).map
              ((CategoryTheory.Functor.uncurry.obj
      (CategoryTheory.Functor.mapBifunctorHomologicalComplex
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.down ℕ) (.down ℕ))).map
        (X := (P.complex, Q.complex)) (Y := (P'.complex, Q'.complex)) (a, b))) 0 ≫
              (e M' N' P' Q').hom := by
  have inst (M N : ModuleCat.{u} R) (P : ProjectiveResolution M)
      (Q : ProjectiveResolution N) : IsIso (columnDesc P Q) := columnDesc_isIso P Q
  refine ⟨fun M N P Q => asIso (columnDesc P Q), ?_⟩
  intro M N M' N' P Q P' Q' f g a b ha hb
  change columnDesc P Q ≫ ChainComplex.tensorMap a g =
    HomologicalComplex.opcyclesMap _ 0 ≫ columnDesc P' Q'
  rw [← CategoryTheory.cancel_epi
    ((((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex).flip.pOpcycles 0)]
  simp only [← Category.assoc, columnDesc, HomologicalComplex.p_descOpcycles]
  erw [HomologicalComplex.p_opcyclesMap, Category.assoc,
    HomologicalComplex.p_descOpcycles]
  ext p
  simp only [HomologicalComplex.comp_f, columnAugmentation, ChainComplex.tensorMap,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id, 
    Functor.uncurry_obj_map,
    Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f,
    flipFunctor_map_f_f, Functor.flip_map_app, curriedTensor_obj_map, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hb]


end HomologicalComplex₂
