/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal

/-!
# The restriction augmentation into total hypercover sections

Source: Stacks Project, Tag 09A2, lemma-compute-cohomology.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u})
  (W : X.ProEt) (U : SimplicialObject (Over W))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the vertices, with scalars restricted from the augmentation object.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
noncomputable def abelianHypercoverRestrictionZero
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj I ⟶
      ((abelianHypercoverSections X W U).obj I).obj ⦋0⦌ :=
  I.obj.map (U _⦋0⦌).hom.op

/-- Restriction to vertices agrees with ordinary sheaf restriction.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
@[simp]
lemma abelianHypercoverRestrictionZero_apply
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1})
    (x : I.obj.obj (op W)) :
    (abelianHypercoverRestrictionZero X W U I).hom x =
      I.obj.map (U _⦋0⦌).hom.op x := by rfl

private theorem abelianHypercoverRestrictionZero_naturality
    {I J : Sheaf (topology X) AddCommGrpCat.{u + 1}}
    (f : I ⟶ J) :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).map f ≫
      abelianHypercoverRestrictionZero X W U J =
      abelianHypercoverRestrictionZero X W U I ≫
        ((abelianHypercoverSections X W U).map f).app ⦋0⦌ := by
  ext x
  simp only [AddCommGrpCat.comp_apply, abelianHypercoverRestrictionZero_apply]
  exact ConcreteCategory.congr_hom (f.hom.naturality (U _⦋0⦌).hom.op).symm x

/-- The restriction to vertices is killed by the alternating face differential.
Source: Stacks Project, Tag 01GE.
(auxiliary; not a blueprint node). -/
theorem abelianHypercoverRestrictionZero_d
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    abelianHypercoverRestrictionZero X W U I ≫
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        ((abelianHypercoverSections X W U).obj I)).d 0 1 = 0 := by
  change abelianHypercoverRestrictionZero X W U I ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val • ((abelianHypercoverSections X W U).obj I).δ j) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    one_smul, ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero]
  ext x
  simp only [AddCommGrpCat.comp_apply, abelianHypercoverRestrictionZero_apply]
  change I.obj.map (U.δ 0).left.op (I.obj.map (U _⦋0⦌).hom.op x) =
    I.obj.map (U.δ 1).left.op (I.obj.map (U _⦋0⦌).hom.op x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have h : (U _⦋0⦌).hom.op ≫ (U.δ 0).left.op =
      (U _⦋0⦌).hom.op ≫ (U.δ 1).left.op := by
    simpa only [← op_comp] using
      congrArg Quiver.Hom.op ((U.δ 0).w.trans (U.δ 1).w.symm)
  rw [h]

/-- Restriction into degree zero of the alternating section complex.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
noncomputable def abelianHypercoverRowAugmentation
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj I ⟶
      ((abelianHypercoverRows X W U).obj I).X 0 :=
  abelianHypercoverRestrictionZero X W U I ≫
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((abelianHypercoverSections X W U).obj I)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl).inv

set_option backward.isDefEq.respectTransparency false in
/-- Restriction into the extended section row is natural in the module sheaf.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
@[reassoc]
lemma abelianHypercoverRowAugmentation_naturality
    {I J : Sheaf (topology X) AddCommGrpCat.{u + 1}}
    (f : I ⟶ J) :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).map f ≫
      abelianHypercoverRowAugmentation X W U J =
      abelianHypercoverRowAugmentation X W U I ≫
        ((abelianHypercoverRows X W U).map f).f 0 := by
  dsimp only [abelianHypercoverRowAugmentation, abelianHypercoverRows, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, abelianHypercoverRestrictionZero_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extended section-row differential kills the augmentation.
Source: Stacks Project, Tag 01GE.
(auxiliary; not a blueprint node). -/
@[reassoc (attr := simp)]
lemma abelianHypercoverRowAugmentation_d
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    abelianHypercoverRowAugmentation X W U I ≫
      ((abelianHypercoverRows X W U).obj I).d 0 1 = 0 := by
  dsimp only [abelianHypercoverRowAugmentation, abelianHypercoverRows, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, abelianHypercoverRestrictionZero_d, zero_comp]

/-- The augmented row, with the augmentation object placed in degree zero.
Source: Stacks Project, Tags 09A2 and 01GE.
(auxiliary; not a blueprint node). -/
noncomputable def abelianHypercoverRowAugmentationComplex
    (I : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    (HomologicalComplex.single _ (.up ℤ) 0).obj
      (((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj I) ⟶
        (abelianHypercoverRows X W U).obj I :=
  HomologicalComplex.mkHomFromSingle (abelianHypercoverRowAugmentation X W U I) (by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact abelianHypercoverRowAugmentation_d X W U I)

-- The total augmentation expands the section, extension and total functors.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical augmentation of a coefficient complex into total hypercover sections.
Its degree-n component is restriction into the (0,n) summand.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
noncomputable def abelianHypercoverAugmentation :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⟶ abelianHypercoverTotal X W U where
  app K := by
    let D := HomologicalComplex₂.flip
      (((abelianHypercoverRows X W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    refine
      { f := fun n ↦ abelianHypercoverRowAugmentation X W U (K.X n) ≫
          D.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
        comm' := ?_ }
    intro n m h
    have hm : n + 1 = m := h
    subst m
    change (abelianHypercoverRowAugmentation X W U (K.X n) ≫
      D.ιTotal (ComplexShape.up ℤ) 0 n n _) ≫ (D.total (ComplexShape.up ℤ)).d n (n + 1) =
        ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).map (K.d n (n + 1)) ≫ _
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1)
      n (n + 1) (by simp [add_comm]), D.d₂_eq (ComplexShape.up ℤ) 0
      (by simp : (ComplexShape.up ℤ).Rel n (n + 1)) (n + 1) (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (0, n) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (0, n) = 1 := by
      change (-1 : ℤˣ) ^ (0 : ℤ) = 1
      exact zpow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc]
    change (_ ≫ ((abelianHypercoverRows X W U).obj (K.X n)).d 0 1) ≫ _ + _ = _
    rw [abelianHypercoverRowAugmentation_d, zero_comp, zero_add]
    exact congrArg (fun z ↦ z ≫ D.ιTotal (ComplexShape.up ℤ) 0 (n + 1) (n + 1)
      (by simp)) (abelianHypercoverRowAugmentation_naturality X W U (K.d n (n + 1))).symm
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    let D := HomologicalComplex₂.flip
      (((abelianHypercoverRows X W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let D' := HomologicalComplex₂.flip
      (((abelianHypercoverRows X W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    let g := (HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((abelianHypercoverRows X W U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    change ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).map (f.f n) ≫
      (abelianHypercoverRowAugmentation X W U (L.X n) ≫ D'.ιTotal (.up ℤ) 0 n n _) =
      (abelianHypercoverRowAugmentation X W U (K.X n) ≫ D.ιTotal (.up ℤ) 0 n n _) ≫
        (HomologicalComplex₂.total.map g (.up ℤ)).f n
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc]
    exact congrArg (fun z ↦ z ≫ D'.ιTotal (.up ℤ) 0 n n (by simp))
      (abelianHypercoverRowAugmentation_naturality X W U (f.f n))

end AlgebraicGeometry.Scheme.ProEt
