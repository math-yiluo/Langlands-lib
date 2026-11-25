/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The braiding of the derived tensor product is symmetric

If the braiding of a monoidal category `C` is symmetric, `β_ Y X ∘ β_ X Y = 𝟙`, then so are:

- the Koszul braiding of cochain complexes `CochainComplex.Monoidal.braiding`
  (`CochainComplex.Monoidal.braiding_hom_braiding_hom`), the two signs `(-1)^(pq)` cancelling;
- the braiding of the homotopy category (`HomotopyCategory.braiding_hom_braiding_hom`);
- the braiding of a derived monoidal category `CategoryTheory.DerivedMonoidal.braidedCategory'`
  (`CategoryTheory.DerivedMonoidal.braiding_hom_braiding_hom`);
- the braiding `DerivedCategory.braidedCategory'` of the derived tensor product on
  `DerivedCategory C` (`DerivedCategory.braiding_hom_braiding_hom`).

The symmetry of `C` is passed as a hypothesis on a given braiding rather than as a
`SymmetricCategory` instance, so that the statements apply to whatever braiding instance is used
for `C` (for instance the braiding of sheaves induced by a symmetric coefficient category).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex.Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The Koszul braiding of cochain complexes over a symmetric category is symmetric. -/
lemma braiding_hom_braiding_hom (hC : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (K L : CochainComplex C ℤ) :
    (braiding K L).hom ≫ (braiding L K).hom = 𝟙 _ := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, ι_braiding_hom_assoc, Preadditive.zsmul_comp, assoc,
    ι_braiding_hom, Preadditive.comp_zsmul, smul_smul, reassoc_of% (hC (K.X p) (L.X q)),
    mul_comm q p, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
    HomologicalComplex.id_f]
  exact (comp_id _).symm

end CochainComplex.Monoidal

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The braiding of the homotopy category over a symmetric category is symmetric. -/
lemma braiding_hom_braiding_hom (hC : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (K L : HomotopyCategory C (.up ℤ)) :
    (β_ K L).hom ≫ (β_ L K).hom = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  have := (quotient C _).congr_map (CochainComplex.Monoidal.braiding_hom_braiding_hom hC K L)
  rw [Functor.map_comp, CategoryTheory.Functor.map_id] at this
  exact this

end HomotopyCategory

namespace CategoryTheory.DerivedMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W]

/-- Over a symmetric category, the two lifts of the braiding coincide. -/
lemma braidingInvNatTrans_eq_braidingNatTrans
    (hC : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _) :
    braidingInvNatTrans L W = braidingNatTrans L W := by
  have h : braidingInvCounit L W = braidingCounit L W := by
    ext X Y
    simp only [braidingInvCounit, braidingCounit, NatTrans.comp_app, Functor.whiskerRight_app]
    congr 2
    ext Y
    exact congrArg (toDerivedMonoidal L W).map (Iso.inv_ext (hC X Y))
  rw [braidingInvNatTrans, braidingNatTrans, h]

/-- Over a symmetric category, the braiding of the derived monoidal category is symmetric. -/
lemma braiding_hom_braiding_hom (hC : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (X Y : DerivedMonoidal L W) :
    (braiding' L W X Y).hom ≫ (braiding' L W Y X).hom = 𝟙 _ := by
  have h : (braiding' L W Y X).hom = (braiding' L W X Y).inv := by
    simp only [braiding', braidingInvNatTrans_eq_braidingNatTrans L W hC]
  rw [h, Iso.hom_inv_id]

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_derivedSymmetric : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The braiding `DerivedCategory.braidedCategory'` of the derived tensor product is symmetric
when the braiding of `C` is. -/
lemma braiding_hom_braiding_hom (hC : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (X Y : DerivedCategory C) :
    letI := braidedCategory' C
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ :=
  DerivedMonoidal.braiding_hom_braiding_hom Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.braiding_hom_braiding_hom hC) X Y

end DerivedCategory
