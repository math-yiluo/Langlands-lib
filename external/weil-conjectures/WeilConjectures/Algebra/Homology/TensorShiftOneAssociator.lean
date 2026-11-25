/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # First-factor translation and the total tensor associator
Source: Stacks Project, Tag 06YH, the homogeneous-summand calculation.
(blueprint: lem-sc-total-tensor-shift-one-associator).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimitsOfSize.{0, 0} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- First-factor translation by one commutes with the total tensor associator.
Source: Stacks Project, Tag 06YH, the homogeneous-summand calculation in
lem-sc-scheme-canonical-tensor-shift-associator-kflat-one.
(blueprint: lem-sc-total-tensor-shift-one-associator).

Proof. Test the two maps on each tridegree summand of the source total complex.
The first-factor shift map has coefficient one. Reassociation applies the module
associator, so either order gives the same map into the target summand, with first
index increased by one. Coproduct extensionality in each degree, followed by
complex extensionality, proves equality. The maps already commute with the
signed differentials by construction of mapBifunctorShift₁Iso. This works also
for zero complexes and in characteristic two. -/
theorem tensorShiftOne_associator (P T U : CochainComplex C ℤ) :
    (α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (mapBifunctorShift₁Iso P (T ⊗ U) (curriedTensor C) 1).hom =
      (mapBifunctorShift₁Iso P T (curriedTensor C) 1).hom ▷ U ≫
        (mapBifunctorShift₁Iso (P ⊗ T) U (curriedTensor C) 1).hom ≫
        (α_ P T U).hom⟦(1 : ℤ)⟧' := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  simp only [HomologicalComplex.comp_f]
  change _ ≫ (HomologicalComplex.mapBifunctorAssociatorX
    (curriedAssociatorNatIso C) (P⟦(1 : ℤ)⟧) T U (.up ℤ) (.up ℤ) (.up ℤ) n).hom ≫ _ =
    _ ≫ _ ≫ _ ≫ (HomologicalComplex.mapBifunctorAssociatorX
      (curriedAssociatorNatIso C) P T U (.up ℤ) (.up ℤ) (.up ℤ) (n + 1)).hom
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  have h₁ : (p + q) + r = n := h
  have h₂ : p + (q + r) = n := by omega
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ (q + r) _ rfl h₂,
    HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ (p + q) _ rfl h₁]
  simp only [Category.assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f P (T ⊗ U) (curriedTensor C) 1
    p (q + r) n h₂ (p + 1) (n + 1) rfl rfl]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  erw [ι_mapBifunctorShift₁Iso_hom_f_assoc (P ⊗ T) U (curriedTensor C) 1
    (p + q) r n h₁ (p + q + 1) (n + 1) rfl rfl]
  dsimp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  simp only [Category.id_comp, Category.comp_id]
  simp only [whiskerLeft_id, Category.id_comp]
  rw [← comp_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f P T (curriedTensor C) 1
    p q (p + q) rfl (p + 1) (p + q + 1) rfl rfl]
  dsimp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  dsimp only [curriedAssociatorNatIso, NatIso.ofComponents]
  erw [id_whiskerRight, id_whiskerRight, id_whiskerRight]
  simp only [Category.id_comp]
  have h₃ : (p + 1 + q) + r = n + 1 := by omega
  have h₄ : (p + 1) + (q + r) = n + 1 := by omega
  have he := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso C) P T U (.up ℤ) (.up ℤ) (.up ℤ)
    (p + 1) q r (n + 1) h₃
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _
    (p + q + 1) _ (by dsimp; omega) (by dsimp; omega),
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _
    (q + r) _ rfl h₄] at he
  erw [Category.comp_id]
  simp only [Category.assoc] at he
  convert he.symm using 1 <;> rfl

end CochainComplex
