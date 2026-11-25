/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Complements on the tensor product of cochain complexes

For cochain complexes indexed by `ℤ`, we describe the differential of the tensor product
`P ⊗ K` and the morphism `P ◁ f` on the summands `P.X p ⊗ K.X q`.

If `G : C ⥤ D` is an additive oplax monoidal functor which preserves the coproducts
defining the tensor product of complexes, the comonoidal structure of `G` induces
a natural transformation `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of bifunctors on homological complexes
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`), which is an
isomorphism when every `δ G X Y` is an isomorphism.

If `C` is braided, so is the category of cochain complexes, with the Koszul sign rule
(`CochainComplex.Monoidal.braidedCategory`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P K : CochainComplex C ℤ)

lemma tensorObj_d_eq (r r' : ℤ) :
    (P ⊗ K).d r r' = (HomologicalComplex.tensorObj P K).d r r' := rfl

variable {K} in
lemma whiskerLeft_f_eq {K' : CochainComplex C ℤ} (f : K ⟶ K') (r : ℤ) :
    (P ◁ f).f r = (HomologicalComplex.tensorHom (𝟙 P) f).f r := rfl

/-- The differential of `P ⊗ K` on the summand `P.X p ⊗ K.X q` of `(P ⊗ K).X r`:
```
P.X p ⊗ K.X q ───────── ιTensorObj ─────────▶ (P ⊗ K).X r
      │                                              │
      │ (d_P ▷ K.X q, (-1)ᵖ • P.X p ◁ d_K)           │ (P ⊗ K).d r r'
      ▼                                              ▼
P.X (p + 1) ⊗ K.X q ⊞ P.X p ⊗ K.X (q + 1) ─ ιTensorObj ─▶ (P ⊗ K).X r'
```
-/
@[reassoc]
lemma ιTensorObj_d (p q r r' : ℤ) (h : p + q = r) (h' : r + 1 = r') :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ⊗ K).d r r' =
      P.d p (p + 1) ▷ K.X q ≫ HomologicalComplex.ιTensorObj P K (p + 1) q r' (by lia) +
        p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
          HomologicalComplex.ιTensorObj P K p (q + 1) r' (by lia)) := by
  rw [tensorObj_d_eq, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = r' by lia),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = r' by lia)]
  simp

variable {K} in
/-- The morphism `P ◁ f` on the summand `P.X p ⊗ K.X q` of `(P ⊗ K).X r`:
```
P.X p ⊗ K.X q  ── ιTensorObj ──▶ (P ⊗ K).X r
      │                               │
      │ P.X p ◁ f.f q                 │ (P ◁ f).f r
      ▼                               ▼
P.X p ⊗ K'.X q ── ιTensorObj ──▶ (P ⊗ K').X r
```
-/
@[reassoc]
lemma ιTensorObj_whiskerLeft_f {K' : CochainComplex C ℤ} (f : K ⟶ K') (p q r : ℤ)
    (h : p + q = r) :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ◁ f).f r =
      P.X p ◁ f.f q ≫ HomologicalComplex.ιTensorObj P K' p q r h := by
  rw [whiskerLeft_f_eq]
  simp

section Bounds

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] (K L : CochainComplex C ℤ) [HomologicalComplex.HasTensor K L]

/-- The tensor product of a complex vanishing below `a` and one vanishing below `c` vanishes
below `a + c`. -/
lemma isStrictlyGE_tensorObj (a c : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE c] :
    IsStrictlyGE (HomologicalComplex.tensorObj K L) (a + c) := by
  rw [isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq ↦ ?_)
  apply IsZero.eq_of_src
  have hpq' : p + q = n := hpq
  by_cases hp : p < a
  · exact ((curriedTensor C).map_isZero (K.isZero_of_isStrictlyGE a p hp)).obj _
  · exact ((curriedTensor C).obj _).map_isZero (L.isZero_of_isStrictlyGE c q (by omega))

/-- The tensor product of a complex vanishing above `b` and one vanishing above `d` vanishes
above `b + d`. -/
lemma isStrictlyLE_tensorObj (b d : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE d] :
    IsStrictlyLE (HomologicalComplex.tensorObj K L) (b + d) := by
  rw [isStrictlyLE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq ↦ ?_)
  apply IsZero.eq_of_src
  have hpq' : p + q = n := hpq
  by_cases hp : b < p
  · exact ((curriedTensor C).map_isZero (K.isZero_of_isStrictlyLE b p hp)).obj _
  · exact ((curriedTensor C).obj _).map_isZero (L.isZero_of_isStrictlyLE d q (by omega))

end Bounds

section Braiding

/-!
### The braiding

If `C` is braided, the tensor product of cochain complexes is braided by the Koszul sign rule:
the braiding `K ⊗ L ≅ L ⊗ K` is `(-1) ^ (p * q) • β_ (K.X p) (L.X q)` on the summand
`K.X p ⊗ L.X q` (`CochainComplex.Monoidal.ι_braiding_hom`). It is obtained from the braiding of
`C` and the symmetry `HomologicalComplex.mapBifunctorFlipIso` of total complexes.
-/

namespace Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable (K L : CochainComplex C ℤ)

/-- The braiding of `C` as an isomorphism between the bicomplexes `(K.X p ⊗ L.X q)` and
`(L.X q ⊗ K.X p)`. -/
noncomputable def braidingBicomplexIso :
    (((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L ≅
      ((((curriedTensor C).flip).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L where
  hom := HomologicalComplex₂.homMk (fun x ↦ (β_ (K.X x.1) (L.X x.2)).hom)
    (fun p p' q _ ↦ (BraidedCategory.braiding_naturality_left _ _).symm)
    (fun p q q' _ ↦ (BraidedCategory.braiding_naturality_right _ _).symm)
  inv := HomologicalComplex₂.homMk (fun x ↦ (β_ (K.X x.1) (L.X x.2)).inv)
    (fun p p' q _ ↦ (BraidedCategory.braiding_inv_naturality_right _ _).symm)
    (fun p q q' _ ↦ (BraidedCategory.braiding_inv_naturality_left _ _).symm)
  hom_inv_id := by ext; simp [HomologicalComplex₂.homMk]
  inv_hom_id := by ext; simp [HomologicalComplex₂.homMk]

/-- The Koszul braiding `K ⊗ L ≅ L ⊗ K` of cochain complexes. -/
noncomputable def braiding : K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex₂.total.mapIso (braidingBicomplexIso K L) (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (curriedTensor C) (.up ℤ)

variable {K L} in
/-- On the summand `K.X p ⊗ L.X q`, the Koszul braiding is the braiding of `C` with sign
`(-1)^(pq)`:
```
K.X p ⊗ L.X q ---ιTensorObj---> (K ⊗ L).X n
      |                              |
(-1)^(pq) • β              (braiding K L).hom.f n
      v                              v
L.X q ⊗ K.X p ---ιTensorObj---> (L ⊗ K).X n
```
-/
@[reassoc]
lemma ι_braiding_hom (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (braiding K L).hom.f n =
      ((p * q).negOnePow : ℤ) • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n (by rw [← h, add_comm])) := by
  have h₁ : HomologicalComplex.ιMapBifunctor K L (curriedTensor C) (.up ℤ) p q n h ≫
      (HomologicalComplex₂.total.map (braidingBicomplexIso K L).hom (.up ℤ)).f n =
        (β_ (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor K L (curriedTensor C).flip (.up ℤ) p q n h :=
    by erw [HomologicalComplex₂.ιTotal_map]; rfl
  simp only [braiding, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom]
  erw [← assoc, h₁]
  rw [assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom, Units.smul_def,
    Preadditive.comp_zsmul, mul_comm p q]
  rfl

variable (M : CochainComplex C ℤ)

omit [BraidedCategory C] in
/-- On the summand `(K.X p ⊗ L.X q) ⊗ M.X r`, the associator is the associator of `C`:
```
(K.X p ⊗ L.X q) ⊗ M.X r ---ι₁₂---> ((K ⊗ L) ⊗ M).X n
          |                                |
          α                         (α_ K L M).hom.f n
          v                                v
K.X p ⊗ (L.X q ⊗ M.X r) ---ι₂₃---> (K ⊗ (L ⊗ M)).X n
```
-/
@[reassoc]
lemma ι₁₂_associator_hom (p q r n : ℤ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ) (.up ℤ)
      p q r n h ≫ (α_ K L M).hom.f n =
    (α_ (K.X p) (L.X q) (M.X r)).hom ≫
      HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ)
        (.up ℤ) (.up ℤ) p q r n h :=
  HomologicalComplex.ι_mapBifunctorAssociatorX_hom _ _ _ _ _ _ _ _ _ _ _ _

omit [BraidedCategory C] in
lemma ι₁₂_eq (p q r s n : ℤ) (hs : p + q = s) (h : s + r = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ) (.up ℤ)
      p q r n (by rw [← h, ← hs]; rfl) =
    (HomologicalComplex.ιTensorObj K L p q s hs ▷ M.X r) ≫
      HomologicalComplex.ιTensorObj (K ⊗ L) M s r n h :=
  HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ hs h

omit [BraidedCategory C] in
lemma ι₂₃_eq (p q r s n : ℤ) (hs : q + r = s) (h : p + s = n) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ) (.up ℤ)
      (.up ℤ) p q r n (by rw [← h, ← hs, ← add_assoc]; rfl) =
    (K.X p ◁ HomologicalComplex.ιTensorObj L M q r s hs) ≫
      HomologicalComplex.ιTensorObj K (L ⊗ M) p s n h :=
  HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hs h

variable {K L M} in
omit [BraidedCategory C] in
/-- On the summand `K.X p ⊗ L.X q`, right whiskering by `f : K ⟶ K'` is `f.f p ▷ L.X q`:
```
K.X p ⊗ L.X q ---ιTensorObj---> (K ⊗ L).X n
      |                              |
f.f p ▷ L.X q                   (f ▷ L).f n
      v                              v
K'.X p ⊗ L.X q --ιTensorObj---> (K' ⊗ L).X n
```
-/
@[reassoc]
lemma ι_whiskerRight {K' : CochainComplex C ℤ} (f : K ⟶ K') (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (f ▷ L).f n =
      (f.f p ▷ L.X q) ≫ HomologicalComplex.ιTensorObj K' L p q n h := by
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- The forward hexagon identity for the Koszul braiding (see `BraidedCategory.hexagon_forward`). -/
lemma hexagon_forward :
    (α_ K L M).hom ≫ (braiding K (L ⊗ M)).hom ≫ (α_ L M K).hom =
      (braiding K L).hom ▷ M ≫ (α_ L K M).hom ≫ L ◁ (braiding K M).hom := by
  ext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  have e₁ := ι₁₂_eq K L M p q r (p + q) n rfl h'
  have e₂ := ι₂₃_eq K L M p q r (q + r) n rfl (by rw [← h', add_assoc])
  have e₃ := ι₁₂_eq L M K q r p (q + r) n rfl (by rw [← h']; omega)
  have e₄ := ι₂₃_eq L M K q r p (p + r) n (add_comm r p) (by rw [← h']; omega)
  have e₅ := ι₁₂_eq L K M q p r (p + q) n (add_comm q p) h'
  have e₆ := ι₂₃_eq L K M q p r (p + r) n rfl (by rw [← h']; omega)
  erw [ι₁₂_associator_hom_assoc]
  rw [e₂, assoc, ι_braiding_hom_assoc]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rw [← assoc (_ ▷ K.X p), ← e₃]
  erw [ι₁₂_associator_hom]
  rw [e₁, assoc, ι_whiskerRight_assoc, ← comp_whiskerRight_assoc, ι_braiding_hom]
  simp only [zsmul_whiskerRight, Preadditive.zsmul_comp,
    comp_whiskerRight, assoc]
  erw [← reassoc_of% e₅]
  erw [ι₁₂_associator_hom_assoc]
  erw [e₆]
  rw [assoc]
  erw [ιTensorObj_whiskerLeft_f]
  rw [← whiskerLeft_comp_assoc]
  erw [ι_braiding_hom]
  simp only [whiskerLeft_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    whiskerLeft_comp, assoc]
  erw [← e₄]
  rw [BraidedCategory.hexagon_forward_assoc, smul_smul, mul_add, Int.negOnePow_add,
    Units.val_mul]

omit [BraidedCategory C] in
/-- On the summand `K.X p ⊗ (L.X q ⊗ M.X r)`, the inverse associator is the one of `C`:
```
K.X p ⊗ (L.X q ⊗ M.X r) ---ι₂₃---> (K ⊗ (L ⊗ M)).X n
          |                                |
         α⁻¹                        (α_ K L M).inv.f n
          v                                v
(K.X p ⊗ L.X q) ⊗ M.X r ---ι₁₂---> ((K ⊗ L) ⊗ M).X n
```
-/
@[reassoc]
lemma ι₂₃_associator_inv (p q r n : ℤ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ)
        (.up ℤ) (.up ℤ) p q r n h ≫ (α_ K L M).inv.f n =
    (α_ (K.X p) (L.X q) (M.X r)).inv ≫
      HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M (.up ℤ)
        (.up ℤ) p q r n h := by
  rw [← cancel_mono ((α_ K L M).hom.f n), assoc, assoc, ← HomologicalComplex.comp_f,
    Iso.inv_hom_id, HomologicalComplex.id_f]
  erw [comp_id, ι₁₂_associator_hom]
  rw [Iso.inv_hom_id_assoc]

/-- The reverse hexagon identity for the Koszul braiding (see `BraidedCategory.hexagon_reverse`). -/
lemma hexagon_reverse :
    (α_ K L M).inv ≫ (braiding (K ⊗ L) M).hom ≫ (α_ M K L).inv =
      K ◁ (braiding L M).hom ≫ (α_ K M L).inv ≫ (braiding K M).hom ▷ L := by
  ext n
  apply HomologicalComplex.mapBifunctor₂₃.hom_ext (c₁₂ := .up ℤ)
  intro p q r h
  have h' : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  have f₁ := ι₂₃_eq K L M p q r (q + r) n rfl (by rw [← h', add_assoc])
  have f₂ := ι₁₂_eq K L M p q r (p + q) n rfl h'
  have f₃ := ι₂₃_eq M K L r p q (p + q) n rfl (by rw [← h']; omega)
  have f₄ := ι₁₂_eq M K L r p q (p + r) n (add_comm r p) (by rw [← h']; omega)
  have f₅ := ι₂₃_eq K M L p r q (q + r) n (add_comm r q) (by rw [← h']; omega)
  have f₆ := ι₁₂_eq K M L p r q (p + r) n rfl (by rw [← h']; omega)
  erw [ι₂₃_associator_inv_assoc]
  rw [f₂, assoc, ι_braiding_hom_assoc]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
  erw [BraidedCategory.braiding_naturality_left_assoc]
  rw [← assoc (_ ◁ _), ← f₃]
  erw [ι₂₃_associator_inv]
  rw [f₁, assoc, ιTensorObj_whiskerLeft_f_assoc, ← whiskerLeft_comp_assoc, ι_braiding_hom]
  simp only [whiskerLeft_zsmul, Preadditive.zsmul_comp,
    whiskerLeft_comp, assoc]
  erw [← reassoc_of% f₅]
  erw [ι₂₃_associator_inv_assoc]
  erw [f₆]
  rw [assoc]
  erw [ι_whiskerRight]
  rw [← comp_whiskerRight_assoc]
  erw [ι_braiding_hom]
  simp only [zsmul_whiskerRight, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    comp_whiskerRight, assoc]
  erw [← f₄]
  rw [BraidedCategory.hexagon_reverse_assoc, smul_smul, add_mul, Int.negOnePow_add,
    Units.val_mul, mul_comm]

variable {K L M} in
lemma braiding_naturality_left {K' : CochainComplex C ℤ} (f : K ⟶ K') :
    f ▷ L ≫ (braiding K' L).hom = (braiding K L).hom ≫ L ◁ f := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  rw [ι_whiskerRight_assoc, ι_braiding_hom, ι_braiding_hom_assoc]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
  rw [ιTensorObj_whiskerLeft_f, BraidedCategory.braiding_naturality_left_assoc]

variable {K L M} in
lemma braiding_naturality_right {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    K ◁ g ≫ (braiding K L').hom = (braiding K L).hom ≫ g ▷ K := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  rw [ιTensorObj_whiskerLeft_f_assoc, ι_braiding_hom, ι_braiding_hom_assoc]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
  rw [ι_whiskerRight, BraidedCategory.braiding_naturality_right_assoc]

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The Koszul braided monoidal structure on cochain complexes. -/
noncomputable instance braidedCategory : BraidedCategory (CochainComplex C ℤ) where
  braiding := braiding
  braiding_naturality_left f _ := braiding_naturality_left f
  braiding_naturality_right _ _ _ g := braiding_naturality_right g
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse

end Monoidal

end Braiding

end CochainComplex

namespace CategoryTheory.Functor.OplaxMonoidal

open HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G]

/-- The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` for homological complexes `K` and `L`, induced
by the comonoidal structure `δ` of an additive oplax monoidal functor `G` which preserves the
coproducts `(K ⊗ L).X n = ∐_{p + q = n} K.X p ⊗ L.X q`. It is
`HomologicalComplex.mapBifunctorComparisonNatTrans` applied to `δNatTrans G`: on the summand
`G(K.X p ⊗ L.X q)` it is given by
```
G(K.X p ⊗ L.X q) ──── G(ιTensorObj) ────▶ G((K ⊗ L).X n)
       │                                       │
       │ δ G (K.X p) (L.X q)                   │ comparison
       ▼                                       ▼
G(K.X p) ⊗ G(L.X q) ─── ιTensorObj ───▶ (G(K) ⊗ G(L)).X n
```
-/
noncomputable def mapHomologicalComplexδNatTrans :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex c)).obj
        (curriedTensor (HomologicalComplex C c)) ⟶
      (((whiskeringLeft₂ _).obj (G.mapHomologicalComplex c)).obj
        (G.mapHomologicalComplex c)).obj (curriedTensor (HomologicalComplex D c)) :=
  mapBifunctorComparisonNatTrans (δNatTrans G) c

@[simp]
lemma mapHomologicalComplexδNatTrans_app_app (K L : HomologicalComplex C c) :
    ((mapHomologicalComplexδNatTrans c G).app K).app L =
      mapBifunctorComparison (δNatTrans G) c K L := rfl

variable [∀ X Y : C, IsIso (δ G X Y)]

instance : IsIso (mapHomologicalComplexδNatTrans c G) :=
  inferInstanceAs (IsIso (mapBifunctorComparisonNatTrans (δNatTrans G) c))

end CategoryTheory.Functor.OplaxMonoidal
