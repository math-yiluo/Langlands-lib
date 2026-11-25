/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # The canonical monoidal structure on degree-zero cochain complexes -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory

section Cochain

variable {C : Type uB} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]

/-- The explicit total-tensor comparison for single complexes in degree zero.
Source: Stacks, Cohomology on Sites, Tag 06YQ.
(auxiliary; not a blueprint node).
It is the composition of the two existing single/bifunctor comparisons. -/
@[irreducible]
noncomputable def singleCochainTensorIso
    (L M : C) :
    (HomologicalComplex.single _ (.up ℤ) 0).obj L ⊗
      (HomologicalComplex.single _ (.up ℤ) 0).obj M ≅
        (HomologicalComplex.single _ (.up ℤ) 0).obj (L ⊗ M) :=
  ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) L).app
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)

private lemma singleCochainTensorIso_inv_f (L M : C) :
    (singleCochainTensorIso L M).inv.f 0 =
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) 0 0 0 rfl := by
  simp [singleCochainTensorIso, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, whiskerLeft_id]

private lemma singleCochainTensorIso_naturality
    {L L' M M' : C} (f : L ⟶ L') (g : M ⟶ M') :
    ((HomologicalComplex.single _ (.up ℤ) 0).map f ⊗ₘ
        (HomologicalComplex.single _ (.up ℤ) 0).map g) ≫
      (singleCochainTensorIso L' M').hom =
    (singleCochainTensorIso L M).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (f ⊗ₘ g) := by
  apply (cancel_epi (singleCochainTensorIso L M).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (singleCochainTensorIso L' M').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, singleCochainTensorIso_inv_f]
  simp only [tensorHom_def, HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]
  simp [HomologicalComplex.single, Category.assoc]

private lemma singleCochainTensorIso_associativity
    (L M N : C) :
    (singleCochainTensorIso L M).hom ▷
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ≫
      (singleCochainTensorIso (L ⊗ M) N).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (α_ L M N).hom =
    (α_ ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N)).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).obj L ◁
        (singleCochainTensorIso M N).hom ≫
      (singleCochainTensorIso L (M ⊗ N)).hom := by
  let sg := HomologicalComplex.single C (.up ℤ) 0
  let el := tensorIso (singleCochainTensorIso L M) (Iso.refl (sg.obj N)) ≪≫
    singleCochainTensorIso (L ⊗ M) N
  let er := tensorIso (Iso.refl (sg.obj L)) (singleCochainTensorIso M N) ≪≫
    singleCochainTensorIso L (M ⊗ N)
  suffices el.hom ≫ sg.map (α_ L M N).hom = (α_ _ _ _).hom ≫ er.hom by
    simpa only [el, er, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id, id_tensorHom, Category.assoc] using this
  apply (cancel_epi el.inv).1
  apply (cancel_mono er.inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  have h := CochainComplex.Monoidal.ι₁₂_associator_hom
    (sg.obj L) (sg.obj M) (sg.obj N) 0 0 0 0 (by simp)
  simp only [CochainComplex.Monoidal.ι₁₂_eq _ _ _ 0 0 0 0 0 rfl rfl,
    CochainComplex.Monoidal.ι₂₃_eq _ _ _ 0 0 0 0 0 rfl rfl] at h
  simpa [el, er, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    tensorHom_id, id_tensorHom, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    whiskerLeft_id, id_whiskerRight, Category.id_comp, Category.comp_id,
    singleCochainTensorIso_inv_f, HomologicalComplex.single, Category.assoc,
    CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f, sg] using h.symm

private lemma singleCochainTensorIso_leftUnitor (L : C) :
    singleCochainTensorIso (𝟙_ _) L ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (λ_ L) =
    λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj L) := by
  apply Iso.ext_inv
  apply HomologicalComplex.from_single_hom_ext
  change _ = (HomologicalComplex.leftUnitor'
    ((HomologicalComplex.single C (.up ℤ) 0).obj L)).inv 0
  simp [Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.comp_f,
    singleCochainTensorIso_inv_f,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, HomologicalComplex.tensorUnit,
    HomologicalComplex.leftUnitor'_inv, id_whiskerRight]

private lemma singleCochainTensorIso_rightUnitor (L : C) :
    singleCochainTensorIso L (𝟙_ _) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (ρ_ L) =
    ρ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj L) := by
  apply Iso.ext_inv
  apply HomologicalComplex.from_single_hom_ext
  change _ = (HomologicalComplex.rightUnitor'
    ((HomologicalComplex.single C (.up ℤ) 0).obj L)).inv 0
  simp [Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.comp_f,
    singleCochainTensorIso_inv_f,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, HomologicalComplex.tensorUnit,
    HomologicalComplex.rightUnitor'_inv, whiskerLeft_id]

@[instance_reducible]
private noncomputable def cochainSingleMonoidal :
    (HomologicalComplex.single C (.up ℤ) 0).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := singleCochainTensorIso
      μIso_hom_natural_left f M := by
        simpa only [(HomologicalComplex.single _ (.up ℤ) 0).map_id, tensorHom_id] using
          singleCochainTensorIso_naturality f (𝟙 M)
      μIso_hom_natural_right L f := by
        simpa only [(HomologicalComplex.single _ (.up ℤ) 0).map_id, id_tensorHom] using
          singleCochainTensorIso_naturality (𝟙 L) f
      associativity := singleCochainTensorIso_associativity
      left_unitality L := by
        simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom,
          id_whiskerRight, Category.id_comp] using
          (congrArg Iso.hom (singleCochainTensorIso_leftUnitor L)).symm
      right_unitality L := by
        simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom,
          whiskerLeft_id, Category.id_comp] using
          (congrArg Iso.hom (singleCochainTensorIso_rightUnitor L)).symm }

/-- The canonical degree-zero cochain tensorator extends to a strong monoidal structure.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU, total tensor of single complexes.
(auxiliary; not a blueprint node).
Proof: the inverse tensorator is the inclusion of the (0,0) summand. Naturality follows
from naturality of this inclusion. The triple inclusion identities give associativity,
and the degree-zero unit inclusions give both unit equations. Apply CoreMonoidal to
these explicit isomorphisms; its tensorator is definitionally the displayed one. -/
theorem exists_singleCochainMonoidal :
    ∃ m : (HomologicalComplex.single C (.up ℤ) 0).Monoidal,
      ∀ L M : C, letI := m
        Functor.LaxMonoidal.μ (HomologicalComplex.single C (.up ℤ) 0) L M =
          (singleCochainTensorIso L M).hom := by
  exact ⟨cochainSingleMonoidal, fun _ _ ↦ rfl⟩

end Cochain

end AlgebraicGeometry.Etale
