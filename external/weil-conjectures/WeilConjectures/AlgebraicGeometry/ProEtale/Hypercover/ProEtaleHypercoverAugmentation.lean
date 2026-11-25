/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverTotal
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative

/-!
# The restriction augmentation into total hypercover sections

## References

* Stacks Project, Tags 09A2 and 01GE
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
  (W : X.ProEt) (U : SimplicialObject (Over W))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the vertices, with scalars restricted from the augmentation object. -/
noncomputable def hypercoverRestrictionZero
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (SheafOfModules.evaluation _ (op W)).obj I ⟶
      ((hypercoverSections X R W U).obj I).obj ⦋0⦌ :=
  by
    dsimp [hypercoverSections, PresheafOfModules.forgetToPresheafModuleCat,
      PresheafOfModules.forgetToPresheafModuleCatObj,
      PresheafOfModules.forgetToPresheafModuleCatObjObj,
      PresheafOfModules.pushforward₀, PresheafOfModules.pushforward₀Obj]
    exact I.val.map (Over.mkIdTerminal.from (U _⦋0⦌)).left.op

/-- Restriction to vertices agrees with ordinary sheaf restriction. -/
@[simp]
lemma hypercoverRestrictionZero_apply
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (x : I.val.obj (op W)) :
    (hypercoverRestrictionZero X R W U I).hom x =
      I.val.map (U _⦋0⦌).hom.op x := by
  exact I.val.congr_map_apply (congrArg Quiver.Hom.op
    (Over.mkIdTerminal_from_left (U _⦋0⦌))) x

private theorem hypercoverRestrictionZero_naturality
    {I J : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
    (f : I ⟶ J) :
    (SheafOfModules.evaluation _ (op W)).map f ≫ hypercoverRestrictionZero X R W U J =
      hypercoverRestrictionZero X R W U I ≫ ((hypercoverSections X R W U).map f).app ⦋0⦌ := by
  ext x
  simp only [ModuleCat.comp_apply, hypercoverRestrictionZero_apply]
  exact (PresheafOfModules.naturality_apply f.val (U _⦋0⦌).hom.op x).symm

/-- The restriction to vertices is killed by the alternating face differential. -/
theorem hypercoverRestrictionZero_d
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    hypercoverRestrictionZero X R W U I ≫
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        ((hypercoverSections X R W U).obj I)).d 0 1 = 0 := by
  change hypercoverRestrictionZero X R W U I ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val • ((hypercoverSections X R W U).obj I).δ j) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    one_smul, ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero]
  ext x
  simp only [ModuleCat.comp_apply, hypercoverRestrictionZero_apply]
  change I.val.map (U.δ 0).left.op (I.val.map (U _⦋0⦌).hom.op x) =
    I.val.map (U.δ 1).left.op (I.val.map (U _⦋0⦌).hom.op x)
  rw [← I.val.map_comp_apply, ← I.val.map_comp_apply]
  have h : (U _⦋0⦌).hom.op ≫ (U.δ 0).left.op =
      (U _⦋0⦌).hom.op ≫ (U.δ 1).left.op := by
    simpa only [← op_comp] using
      congrArg Quiver.Hom.op ((U.δ 0).w.trans (U.δ 1).w.symm)
  rw [h]

/-- Restriction into degree zero of the alternating section complex. -/
noncomputable def hypercoverRowAugmentation
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (SheafOfModules.evaluation _ (op W)).obj I ⟶
      ((hypercoverSectionRows X R W U).obj I).X 0 :=
  hypercoverRestrictionZero X R W U I ≫
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((hypercoverSections X R W U).obj I)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl).inv

set_option backward.isDefEq.respectTransparency false in
/-- Restriction into the extended section row is natural in the module sheaf. -/
@[reassoc]
lemma hypercoverRowAugmentation_naturality
    {I J : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
    (f : I ⟶ J) :
    (SheafOfModules.evaluation _ (op W)).map f ≫ hypercoverRowAugmentation X R W U J =
      hypercoverRowAugmentation X R W U I ≫
        ((hypercoverSectionRows X R W U).map f).f 0 := by
  dsimp only [hypercoverRowAugmentation, hypercoverSectionRows, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hypercoverRestrictionZero_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extended section-row differential kills the augmentation. -/
@[reassoc (attr := simp)]
lemma hypercoverRowAugmentation_d
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    hypercoverRowAugmentation X R W U I ≫
      ((hypercoverSectionRows X R W U).obj I).d 0 1 = 0 := by
  dsimp only [hypercoverRowAugmentation, hypercoverSectionRows, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hypercoverRestrictionZero_d, zero_comp]

/-- The augmented row, with the augmentation object placed in degree zero. -/
noncomputable def hypercoverRowAugmentationComplex
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (HomologicalComplex.single _ (.up ℤ) 0).obj
      ((SheafOfModules.evaluation _ (op W)).obj I) ⟶
        (hypercoverSectionRows X R W U).obj I :=
  HomologicalComplex.mkHomFromSingle (hypercoverRowAugmentation X R W U I) (by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact hypercoverRowAugmentation_d X R W U I)

-- The total augmentation expands the section, extension and total functors.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical augmentation of a coefficient complex into total hypercover sections.
Its degree-n component is restriction into the (0,n) summand. -/
noncomputable def hypercoverAugmentation :
    (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⟶ hypercoverTotal X R W U where
  app K := by
    let D := HomologicalComplex₂.flip
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    refine
      { f := fun n ↦ hypercoverRowAugmentation X R W U (K.X n) ≫
          D.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
        comm' := ?_ }
    intro n m h
    have hm : n + 1 = m := h
    subst m
    change (hypercoverRowAugmentation X R W U (K.X n) ≫
      D.ιTotal (ComplexShape.up ℤ) 0 n n _) ≫ (D.total (ComplexShape.up ℤ)).d n (n + 1) =
        (SheafOfModules.evaluation _ (op W)).map (K.d n (n + 1)) ≫ _
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
    change (_ ≫ ((hypercoverSectionRows X R W U).obj (K.X n)).d 0 1) ≫ _ + _ = _
    rw [hypercoverRowAugmentation_d, zero_comp, zero_add]
    exact congrArg (fun z ↦ z ≫ D.ιTotal (ComplexShape.up ℤ) 0 (n + 1) (n + 1)
      (by simp)) (hypercoverRowAugmentation_naturality X R W U (K.d n (n + 1))).symm
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    let D := HomologicalComplex₂.flip
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let D' := HomologicalComplex₂.flip
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    let g := (HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    change (SheafOfModules.evaluation _ (op W)).map (f.f n) ≫
      (hypercoverRowAugmentation X R W U (L.X n) ≫ D'.ιTotal (.up ℤ) 0 n n _) =
      (hypercoverRowAugmentation X R W U (K.X n) ≫ D.ιTotal (.up ℤ) 0 n n _) ≫
        (HomologicalComplex₂.total.map g (.up ℤ)).f n
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc]
    exact congrArg (fun z ↦ z ≫ D'.ιTotal (.up ℤ) 0 n n (by simp))
      (hypercoverRowAugmentation_naturality X R W U (f.f n))

end AlgebraicGeometry.Scheme.ProEt
