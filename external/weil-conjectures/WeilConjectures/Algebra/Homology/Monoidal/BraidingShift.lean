/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The Koszul braiding of cochain complexes commutes with the shifts

For cochain complexes `K`, `L` over a braided monoidal preadditive category, the Koszul braiding
`β_ K L : K ⊗ L ≅ L ⊗ K` is compatible with the shift isomorphisms of the tensor product
(`CochainComplex.mapBifunctorShift₁Iso`, without signs, and
`CochainComplex.mapBifunctorShift₂Iso`, with the sign `(-1) ^ (p * y)` on the summand
`K.X p ⊗ L.X q`): the square
```
K ⊗ L⟦y⟧ ──── β ────▶ L⟦y⟧ ⊗ K
   │                     │
   ▼                     ▼
(K ⊗ L)⟦y⟧ ──β⟦y⟧──▶ (L ⊗ K)⟦y⟧
```
commutes (`CochainComplex.Monoidal.braiding_hom_mapBifunctorShift₁Iso_hom`). On the summand
`K.X p ⊗ L.X (q + y)` both paths are `(-1) ^ (p * q) • β`: the Koszul sign `(-1) ^ (p * (q + y))`
of `β⟦y⟧` and the shift sign `(-1) ^ (p * y)` combine to the Koszul sign of `β`.
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

/-- The Koszul braiding commutes with the shift isomorphisms of the tensor product of cochain
complexes. -/
lemma braiding_hom_mapBifunctorShift₁Iso_hom (K L : CochainComplex C ℤ) (y : ℤ) :
    (braiding K (L⟦y⟧)).hom ≫
        (CochainComplex.mapBifunctorShift₁Iso L K (curriedTensor C) y).hom =
      (CochainComplex.mapBifunctorShift₂Iso K L (curriedTensor C) y).hom ≫
        (shiftFunctor _ y).map (braiding K L).hom := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  have h' : p + q = n := h
  rw [ι_braiding_hom_assoc (K := K) (L := L⟦y⟧) p q n h', Preadditive.zsmul_comp,
    Category.assoc,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f L K (curriedTensor C) y q p n
      (by rw [← h', add_comm]) (q + y) (n + y) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc K L (curriedTensor C) y p q n h'
      (q + y) (n + y) rfl rfl]
  erw [CochainComplex.shiftFunctor_map_f']
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Iso.refl_inv, Category.comp_id, Units.smul_def, Preadditive.zsmul_comp,
    Category.assoc]
  erw [ι_braiding_hom (K := K) (L := L) p (q + y) (n + y) (by omega)]
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp]
  have hs : (p * y + p * (q + y)).negOnePow = (p * q).negOnePow := by
    rw [Int.negOnePow_eq_iff]
    rw [mul_add]
    generalize p * y = t
    generalize p * q = s
    exact ⟨t, by omega⟩
  erw [smul_smul, ← Units.val_mul, ← Int.negOnePow_add, hs]
  rfl

end CochainComplex.Monoidal
