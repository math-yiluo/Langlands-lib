/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The internal hom of cochain complexes

Let `C` be a monoidal closed preadditive category (with `MonoidalPreadditive C`) which has
countable products. For cochain complexes `P` and `Y` in `C` indexed by `ℤ`, we construct the
internal hom complex `CochainComplex.internalHomObj P Y`, whose object in degree `n` is
`∏_{p + n = q} (P.X p ⟶[C] Y.X q)`, and whose differential has component
`(-1) ^ p • (f_{p, q - 1} ≫ d_Y - d_P ≫ f_{p + 1, q})` on the factor indexed by `(p, q)`
(`internalHomObj_d_π`). The projections to the factors are `internalHomπ`.

When the tensor product of cochain complexes is defined (the `GradedObject` hypotheses of
`Mathlib.Algebra.Homology.Monoidal`), we construct the tensor-hom adjunction
`CochainComplex.tensorHomAdjunction P : tensorLeft P ⊣ CochainComplex.internalHom P`. Its unit
and counit are the coevaluation `K ⟶ internalHomObj P (P ⊗ K)` and the evaluation
`P ⊗ internalHomObj P Y ⟶ Y`.

The hom bijection is obtained from an isomorphism of groups of cochains
`CochainComplex.InternalHom.cochainEquiv P Y K n` between `Cochain (P ⊗ K) Y n` and
`Cochain K (internalHomObj P Y) n`, which sends a cochain `z` to the cochain whose component
on `P.X p ⊗ K.X q` is `(-1) ^ (p * n)` times the curry of the component of `z`, and which
commutes with the differentials of the hom complexes (`curryCochain_δ`). It sends cocycles of
degree `0` (i.e. morphisms of complexes) to cocycles of degree `0`, and coboundaries to
coboundaries, so that the tensor-hom bijection is compatible with homotopies
(`Homotopy.internalHomEquiv`); this is used in
`WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom` to descend the adjunction to
the homotopy category.

## Sign conventions

The tensor product in `Mathlib.Algebra.Homology.Monoidal` has differential
`d_P ▷ _ + (-1) ^ p • _ ◁ d_K` on `P.X p ⊗ K.X q`. With the sign `(-1) ^ p` in the differential
of `internalHomObj P Y`, the hom bijection on morphisms of complexes (cochains of degree `0`) is
plain currying; on cochains of degree `n` the sign `(-1) ^ (p * n)` is then needed for the
compatibility with `δ`.

## Implementation notes

`internalHomObj P Y` is the product totalisation of the bicomplex
`(p, q) ↦ (ihom (P.X p)).obj (Y.X q)`, i.e. of the bifunctor `ihom` applied to `P` and `Y`.
Mathlib only has the coproduct totalisation `HomologicalComplex.mapBifunctor`; once its
product dual exists, `internalHomObj` and its API (`internalHomπ`, `internalHomObj_hom_ext`,
`internalHomObj_d_π`) should become a special case of it.

We assume `HasCountableProducts C` for convenience: only products indexed by the countable
types `HomComplex.Triplet n` are used, and countable products exist in the intended
application to Grothendieck abelian categories.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open MonoidalClosed hiding assoc id_comp comp_id

universe v u

namespace CochainComplex

open HomComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [HasCountableProducts C]

namespace InternalHom

/-- The differential of the internal hom complex `internalHomObj P Y`. Use
`internalHomObj_d_π` instead of unfolding it. -/
noncomputable def d (P Y : CochainComplex C ℤ) (n m : ℤ) :
    (∏ᶜ fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)) ⟶
      ∏ᶜ fun T : Triplet m ↦ (ihom (P.X T.p)).obj (Y.X T.q) :=
  Pi.lift fun T ↦ T.p.negOnePow •
    (Pi.π (fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)) ⟨T.p, T.p + n, rfl⟩ ≫
        (ihom _).map (Y.d (T.p + n) T.q) -
      Pi.π (fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q))
          ⟨T.p + m - n, T.q, by grind [T.hpq]⟩ ≫
        (pre (P.d T.p (T.p + m - n))).app _)

lemma d_π (P Y : CochainComplex C ℤ) (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ)
    (hq' : p + n = q') (hp' : p' + n = q) :
    d P Y n m ≫ Pi.π _ (⟨p, q, hpq⟩ : Triplet m) = p.negOnePow •
      (Pi.π (fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)) ⟨p, q', hq'⟩ ≫
          (ihom _).map (Y.d q' q) -
        Pi.π (fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)) ⟨p', q, hp'⟩ ≫
          (pre (P.d p p')).app _) := by
  subst hq'
  obtain rfl : p' = p + m - n := by lia
  simp only [d, Pi.lift_comp_π]

variable [MonoidalPreadditive C] (P Y : CochainComplex C ℤ)

lemma shape (n m : ℤ) (hnm : ¬ n + 1 = m) : d P Y n m = 0 := by
  refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
  rw [d_π P Y n m p q hpq (p + n) (p + m - n) rfl (by lia), Y.shape, P.shape]
  · simp
  all_goals
    simp only [ComplexShape.up_Rel]
    lia

lemma d_comp_d (n₁ n₂ n₃ : ℤ) : d P Y n₁ n₂ ≫ d P Y n₂ n₃ = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂
  · by_cases h₂₃ : n₂ + 1 = n₃
    · refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
      rw [assoc, d_π P Y n₂ n₃ p q hpq (q - 1) (p + 1) (by lia) (by lia), Linear.comp_units_smul,
        Preadditive.comp_sub, reassoc_of% (d_π P Y n₁ n₂ p (q - 1) (by lia) (q - 2) (p + 1)
          (by lia) (by lia)), reassoc_of% (d_π P Y n₁ n₂ (p + 1) q (by lia) (q - 1) (p + 2)
          (by lia) (by lia))]
      simp only [Linear.units_smul_comp, Preadditive.sub_comp, assoc, ← Functor.map_comp,
        HomologicalComplex.d_comp_d, Functor.map_zero, comp_zero, ← NatTrans.comp_app, ← pre_map,
        pre_zero_app, zero_comp, pre_comm_ihom_map, zero_sub, Int.negOnePow_succ,
        Units.neg_smul, Preadditive.neg_comp, smul_neg, smul_sub, smul_smul,
        Int.units_mul_self, one_smul]
      abel
    · rw [shape P Y n₂ n₃ h₂₃, comp_zero]
  · rw [shape P Y n₁ n₂ h₁₂, zero_comp]

end InternalHom

variable [MonoidalPreadditive C] (P Y : CochainComplex C ℤ)

/-- The internal hom complex of two cochain complexes: in degree `n`, it is the product
of the internal homs `P.X p ⟶[C] Y.X q` for `p + n = q`. -/
noncomputable def internalHomObj : CochainComplex C ℤ where
  X n := ∏ᶜ fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)
  d := InternalHom.d P Y
  shape n m h := InternalHom.shape P Y n m h
  d_comp_d' _ _ _ _ _ := InternalHom.d_comp_d P Y _ _ _

/-- The projection from the object of degree `n` of `internalHomObj P Y` to the factor
`P.X p ⟶[C] Y.X q`, for `p + n = q`. -/
noncomputable def internalHomπ (n p q : ℤ) (h : p + n = q) :
    (internalHomObj P Y).X n ⟶ (ihom (P.X p)).obj (Y.X q) :=
  Pi.π _ (⟨p, q, h⟩ : Triplet n)

variable {P Y} in
@[ext]
lemma internalHomObj_hom_ext {A : C} {n : ℤ} {f g : A ⟶ (internalHomObj P Y).X n}
    (h : ∀ p q hpq, f ≫ internalHomπ P Y n p q hpq = g ≫ internalHomπ P Y n p q hpq) :
    f = g :=
  Pi.hom_ext _ _ fun T ↦ h T.p T.q T.hpq

/-- The components of the differential of the internal hom complex, where `[A, B]` denotes
`(ihom A).obj B`:
```
(internalHomObj P Y).X n ──── d n m ────▶ (internalHomObj P Y).X m
         │                                         │
         │ (-1)ᵖ • (π_{p,q'} ≫ [P.X p, d_Y]         │ π_{p,q}
         │          - π_{p',q} ≫ [d_P, Y.X q])      │
         ╰───────────────────────────────▶ [P.X p, Y.X q]
```
-/
@[reassoc]
lemma internalHomObj_d_π (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ) (hq' : p + n = q')
    (hp' : p' + n = q) :
    (internalHomObj P Y).d n m ≫ internalHomπ P Y m p q hpq = p.negOnePow •
      (internalHomπ P Y n p q' hq' ≫ (ihom _).map (Y.d q' q) -
        internalHomπ P Y n p' q hp' ≫ (pre (P.d p p')).app _) :=
  InternalHom.d_π P Y n m p q hpq q' p' hq' hp'

end

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {P Y : CochainComplex C ℤ} (K : CochainComplex C ℤ)

namespace InternalHom

open HomologicalComplex

variable {K} in
/-- The cochain `K ⟶ internalHomObj P Y` of degree `n` corresponding to a cochain
`P ⊗ K ⟶ Y` of degree `n`: its component `K.X q ⟶ P.X p ⟶[C] Y.X (p + q + n)` is the
curried component `P.X p ⊗ K.X q ⟶ Y.X (p + q + n)`, with the sign `(-1) ^ (p * n)`. -/
noncomputable def curryCochain {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    Cochain K (internalHomObj P Y) n :=
  Cochain.mk fun q _ _ ↦ Pi.lift fun T ↦ (T.p * n).negOnePow •
    curry (ιTensorObj P K T.p q (T.p + q) rfl ≫ z.v (T.p + q) T.q (by grind [T.hpq]))

variable {K} in
/-- The inverse of `curryCochain`. -/
noncomputable def uncurryCochain {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    Cochain (P ⊗ K) Y n :=
  Cochain.mk fun r s hrs ↦ mapBifunctorDesc fun p q (hpq : p + q = r) ↦ (p * n).negOnePow •
    uncurry (w.v q (s - p) (by lia) ≫ internalHomπ P Y (s - p) p s (by lia))

variable {K}

/-- The components of `curryCochain z`, where `[A, B]` denotes `(ihom A).obj B`: the composition
```
K.X q ── (curryCochain z).v q q' ──▶ (internalHomObj P Y).X q' ── π_{p,s} ──▶ [P.X p, Y.X s]
```
is `(-1) ^ (p * n)` times the curry of the composition
```
P.X p ⊗ K.X q ── ιTensorObj ──▶ (P ⊗ K).X r ── z.v r s ──▶ Y.X s
```
-/
@[reassoc]
lemma curryCochain_v_π {n : ℤ} (z : Cochain (P ⊗ K) Y n) (q q' : ℤ) (hqq' : q + n = q')
    (p s : ℤ) (hps : p + q' = s) (r : ℤ) (hr : p + q = r) (hrs : r + n = s) :
    (curryCochain z).v q q' hqq' ≫ internalHomπ P Y q' p s hps =
      (p * n).negOnePow • curry (ιTensorObj P K p q r hr ≫ z.v r s hrs) := by
  subst hr
  exact Pi.lift_comp_π _ _

/-- The components of `uncurryCochain w`, where `[A, B]` denotes `(ihom A).obj B`: the
composition
```
P.X p ⊗ K.X q ── ιTensorObj ──▶ (P ⊗ K).X r ── (uncurryCochain w).v r s ──▶ Y.X s
```
is `(-1) ^ (p * n)` times the uncurry of the composition
```
K.X q ── w.v q q' ──▶ (internalHomObj P Y).X q' ── π_{p,s} ──▶ [P.X p, Y.X s]
```
-/
@[reassoc]
lemma ι_uncurryCochain_v {n : ℤ} (w : Cochain K (internalHomObj P Y) n) (r s : ℤ)
    (hrs : r + n = s) (p q : ℤ) (hpq : p + q = r) (q' : ℤ) (hqq' : q + n = q')
    (hps : p + q' = s) :
    ιTensorObj P K p q r hpq ≫ (uncurryCochain w).v r s hrs =
      (p * n).negOnePow • uncurry (w.v q q' hqq' ≫ internalHomπ P Y q' p s hps) := by
  obtain rfl : q' = s - p := by lia
  rw [uncurryCochain, Cochain.mk_v, ι_mapBifunctorDesc]

variable (P Y K) in
/-- The bijection between cochains `P ⊗ K ⟶ Y` of degree `n` and cochains
`K ⟶ internalHomObj P Y` of degree `n`. -/
noncomputable def cochainEquiv (n : ℤ) :
    Cochain (P ⊗ K) Y n ≃+ Cochain K (internalHomObj P Y) n where
  toFun := curryCochain
  invFun := uncurryCochain
  left_inv z := by
    ext r s hrs
    apply mapBifunctor.hom_ext
    intro p q hpq
    replace hpq : p + q = r := hpq
    rw [ι_uncurryCochain_v _ r s hrs p q hpq (q + n) rfl (by lia),
      curryCochain_v_π _ q (q + n) rfl p s (by lia) r hpq hrs, uncurry_units_smul, uncurry_curry,
      smul_smul, Int.units_mul_self, one_smul]
  right_inv w := by
    ext q q' hqq' p s hps
    rw [curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      ι_uncurryCochain_v _ (p + q) s (by lia) p q rfl q' hqq' hps, curry_units_smul, curry_uncurry,
      smul_smul, Int.units_mul_self, one_smul]
  map_add' z z' := by
    ext q q' hqq' p s hps
    rw [Cochain.add_v, Preadditive.add_comp,
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.add_v,
      Preadditive.comp_add, curry_add, smul_add]

@[simp]
lemma cochainEquiv_apply {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    cochainEquiv P Y K n z = curryCochain z := rfl

@[simp]
lemma cochainEquiv_symm_apply {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    (cochainEquiv P Y K n).symm w = uncurryCochain w := rfl

@[simp]
lemma curryCochain_uncurryCochain {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    curryCochain (uncurryCochain w) = w :=
  (cochainEquiv P Y K n).apply_symm_apply w

@[simp]
lemma uncurryCochain_curryCochain {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    uncurryCochain (curryCochain z) = z :=
  (cochainEquiv P Y K n).symm_apply_apply z

/-- `curryCochain` commutes with the differentials of the hom complexes:
```
Cochain (P ⊗ K) Y n ── curryCochain ──▶ Cochain K (internalHomObj P Y) n
        │                                         │
        │ δ n m                                   │ δ n m
        ▼                                         ▼
Cochain (P ⊗ K) Y m ── curryCochain ──▶ Cochain K (internalHomObj P Y) m
```
-/
lemma curryCochain_δ (n m : ℤ) (z : Cochain (P ⊗ K) Y n) :
    curryCochain (δ n m z) = δ n m (curryCochain z) := by
  by_cases hnm : n + 1 = m
  · subst hnm
    ext q q' hqq' p s hps
    rw [curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      δ_v n (n + 1) rfl z (p + q) s (by lia) (s - 1) (p + q + 1) (by lia) rfl,
      δ_v n (n + 1) rfl (curryCochain z) q q' hqq' (q' - 1) (q + 1) rfl rfl,
      Preadditive.add_comp, assoc, internalHomObj_d_π P Y (q' - 1) q' p s hps (s - 1) (p + 1)
        (by lia) (by lia), Linear.units_smul_comp, assoc,
      curryCochain_v_π _ (q + 1) q' (by lia) p s hps (p + q + 1) (by lia) (by lia),
      Linear.comp_units_smul, Preadditive.comp_sub, ← assoc, ← assoc,
      curryCochain_v_π _ q (q' - 1) (by lia) p (s - 1) (by lia) (p + q) rfl (by lia),
      curryCochain_v_π _ q (q' - 1) (by lia) (p + 1) s (by lia) (p + q + 1) (by lia) (by lia)]
    simp only [← curry_natural_right, curry_pre_app, ← curry_natural_left, Preadditive.comp_add,
      Linear.comp_units_smul, assoc, ιTensorObj_d_assoc P K p q (p + q) (p + q + 1) rfl rfl,
      Linear.units_smul_comp, ← curry_units_smul, ← curry_sub, ← curry_add]
    congr 1
    simp only [Preadditive.add_comp, Linear.units_smul_comp, assoc, smul_add, smul_sub, smul_smul,
      mul_add, add_mul, mul_one, one_mul, Int.negOnePow_add, Int.negOnePow_one, mul_neg, neg_mul,
      Units.neg_smul, smul_neg, mul_comm _ p.negOnePow, mul_left_comm _ p.negOnePow, ← mul_assoc,
      Int.units_mul_self, mul_comm n.negOnePow]
    abel
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    exact (cochainEquiv P Y K m).map_zero

/-- `uncurryCochain` commutes with the differentials of the hom complexes. -/
lemma uncurryCochain_δ (n m : ℤ) (w : Cochain K (internalHomObj P Y) n) :
    uncurryCochain (δ n m w) = δ n m (uncurryCochain w) :=
  (cochainEquiv P Y K m).injective (by
    rw [cochainEquiv_apply, cochainEquiv_apply, curryCochain_δ, curryCochain_uncurryCochain,
      curryCochain_uncurryCochain])

/-- `curryCochain` is natural in the source complex: for `f : K' ⟶ K`, the square
```
Cochain (P ⊗ K) Y n ── curryCochain ──▶ Cochain K (internalHomObj P Y) n
        │                                         │
        │ (P ◁ f) ≫ -                             │ f ≫ -
        ▼                                         ▼
Cochain (P ⊗ K') Y n ─ curryCochain ─▶ Cochain K' (internalHomObj P Y) n
```
commutes. -/
lemma curryCochain_ofHom_whiskerLeft_comp {K' : CochainComplex C ℤ} (f : K' ⟶ K) {n : ℤ}
    (z : Cochain (P ⊗ K) Y n) :
    curryCochain ((Cochain.ofHom (P ◁ f)).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (curryCochain z) (zero_add n) := by
  ext q q' hqq' p s hps
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, assoc,
    curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
    curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ιTensorObj_whiskerLeft_f_assoc, curry_natural_left, Linear.comp_units_smul]

end InternalHom

open InternalHom

variable (P Y) in
/-- The tensor-hom bijection `(P ⊗ K ⟶ Y) ≃ (K ⟶ internalHomObj P Y)` for cochain
complexes. -/
noncomputable def internalHomEquiv : (P ⊗ K ⟶ Y) ≃ (K ⟶ internalHomObj P Y) where
  toFun f := Cocycle.homOf (Cocycle.mk (curryCochain (Cochain.ofHom f)) 1 (zero_add 1) (by
    rw [← curryCochain_δ, δ_ofHom, ← cochainEquiv_apply, map_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (uncurryCochain (Cochain.ofHom g)) 1 (zero_add 1) (by
    rw [← uncurryCochain_δ, δ_ofHom, ← cochainEquiv_symm_apply, map_zero]))
  left_inv f := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, uncurryCochain_curryCochain])
  right_inv g := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, curryCochain_uncurryCochain])

@[simp]
lemma ofHom_internalHomEquiv (f : P ⊗ K ⟶ Y) :
    Cochain.ofHom (internalHomEquiv P Y K f) = curryCochain (Cochain.ofHom f) := by
  simp [internalHomEquiv]

@[simp]
lemma ofHom_internalHomEquiv_symm (g : K ⟶ internalHomObj P Y) :
    Cochain.ofHom ((internalHomEquiv P Y K).symm g) = uncurryCochain (Cochain.ofHom g) := by
  simp [internalHomEquiv]

/-- The tensor-hom bijection is natural in the source complex: for `f : K' ⟶ K` and
`g : P ⊗ K ⟶ Y`, the morphisms
```
P ⊗ K' ── P ◁ f ──▶ P ⊗ K ── g ──▶ Y
K' ── f ──▶ K ── internalHomEquiv g ──▶ internalHomObj P Y
```
correspond to each other under `internalHomEquiv`. -/
lemma internalHomEquiv_whiskerLeft_comp {K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (g : P ⊗ K ⟶ Y) :
    internalHomEquiv P Y K' (P ◁ f ≫ g) = f ≫ internalHomEquiv P Y K g :=
  Cochain.ofHom_injective (by
    rw [ofHom_internalHomEquiv, Cochain.ofHom_comp, Cochain.ofHom_comp, ofHom_internalHomEquiv,
      curryCochain_ofHom_whiskerLeft_comp])

/-- The components of `internalHomEquiv P Y K g` are the curried components of `g`. -/
@[reassoc]
lemma internalHomEquiv_f_π (g : P ⊗ K ⟶ Y) (q p s : ℤ) (hps : p + q = s) :
    (internalHomEquiv P Y K g).f q ≫ internalHomπ P Y q p s hps =
      curry (HomologicalComplex.ιTensorObj P K p q s hps ≫ g.f s) := by
  rw [← Cochain.ofHom_v, ofHom_internalHomEquiv,
    curryCochain_v_π _ q q (add_zero q) p s hps s hps (add_zero s), Cochain.ofHom_v, mul_zero,
    Int.negOnePow_zero, one_smul]

/-- The components of `(internalHomEquiv P Y K).symm g` are the uncurried components of `g`. -/
@[reassoc]
lemma ιTensorObj_internalHomEquiv_symm_f (g : K ⟶ internalHomObj P Y) (p q s : ℤ)
    (hps : p + q = s) :
    HomologicalComplex.ιTensorObj P K p q s hps ≫ ((internalHomEquiv P Y K).symm g).f s =
      uncurry (g.f q ≫ internalHomπ P Y q p s hps) := by
  rw [← Cochain.ofHom_v, ofHom_internalHomEquiv_symm,
    ι_uncurryCochain_v _ s s (add_zero s) p q hps q (add_zero q) hps, Cochain.ofHom_v, mul_zero,
    Int.negOnePow_zero, one_smul]

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (P) in
/-- The internal hom functor `Y ↦ internalHomObj P Y` on cochain complexes, the right adjoint
of `P ⊗ -`. -/
noncomputable def internalHom : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft P) (G_obj := internalHomObj P)
    (fun K Y ↦ internalHomEquiv P Y K) (fun _ _ _ f g ↦ internalHomEquiv_whiskerLeft_comp _ f g)

variable (P) in
/-- The tensor-hom adjunction `P ⊗ - ⊣ internalHom P` on cochain complexes. -/
noncomputable def tensorHomAdjunction : tensorLeft P ⊣ internalHom P :=
  Adjunction.adjunctionOfEquivRight _ _

@[simp]
lemma internalHom_obj : (internalHom P).obj Y = internalHomObj P Y := rfl

/-- The hom bijection of `tensorHomAdjunction P` is `internalHomEquiv`. -/
@[simp]
lemma tensorHomAdjunction_homEquiv (f : P ⊗ K ⟶ Y) :
    (tensorHomAdjunction P).homEquiv K Y f = internalHomEquiv P Y K f := by
  simp [tensorHomAdjunction, Adjunction.adjunctionOfEquivRight, Adjunction.mkOfHomEquiv_homEquiv]

/-- The counit of `tensorHomAdjunction P` is the evaluation `P ⊗ internalHomObj P Y ⟶ Y`, which
corresponds to the identity of `internalHomObj P Y` under the tensor-hom bijection. -/
lemma tensorHomAdjunction_counit_app :
    (tensorHomAdjunction P).counit.app Y = (internalHomEquiv P Y _).symm (𝟙 _) :=
  rfl

/-- The internal hom functor on morphisms: `(internalHom P).map k` corresponds under the
tensor-hom bijection to the evaluation followed by `k`. -/
lemma internalHom_map {Y' : CochainComplex C ℤ} (k : Y ⟶ Y') :
    (internalHom P).map k =
      internalHomEquiv P Y' _ ((tensorHomAdjunction P).counit.app Y ≫ k) := by
  rfl

/-- The components of `(internalHom P).map k`, where `[A, B]` denotes `(ihom A).obj B`:
```
(internalHomObj P Y).X n ── ((internalHom P).map k).f n ──▶ (internalHomObj P Y').X n
         │                                                          │
         │ π_{p,q}                                                  │ π_{p,q}
         ▼                                                          ▼
   [P.X p, Y.X q] ─────────── [P.X p, k.f q] ─────────────▶ [P.X p, Y'.X q]
```
-/
@[reassoc (attr := simp)]
lemma internalHom_map_f_π {Y' : CochainComplex C ℤ} (k : Y ⟶ Y') (n p q : ℤ) (h : p + n = q) :
    ((internalHom P).map k).f n ≫ internalHomπ P Y' n p q h =
      internalHomπ P Y n p q h ≫ (ihom (P.X p)).map (k.f q) := by
  rw [internalHom_map, internalHomEquiv_f_π, HomologicalComplex.comp_f, ← assoc,
    tensorHomAdjunction_counit_app]
  dsimp only [internalHom_obj]
  rw [ιTensorObj_internalHomEquiv_symm_f, curry_natural_right,
    HomologicalComplex.id_f, id_comp, curry_uncurry]

end CochainComplex

namespace Homotopy

open CochainComplex HomComplex InternalHom

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {P Y K : CochainComplex C ℤ}

/-- The tensor-hom bijection sends homotopic morphisms to homotopic morphisms. -/
noncomputable def internalHomEquiv {f f' : P ⊗ K ⟶ Y} (h : Homotopy f f') :
    Homotopy (CochainComplex.internalHomEquiv P Y K f) (CochainComplex.internalHomEquiv P Y K f') :=
  (Cochain.equivHomotopy _ _).symm ⟨curryCochain (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv, ofHom_internalHomEquiv, ← curryCochain_δ, δ_ofHomotopy,
      ← cochainEquiv_apply, ← cochainEquiv_apply, ← cochainEquiv_apply, ← map_add,
      sub_add_cancel]⟩

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (P) in
/-- The internal hom functor `CochainComplex.internalHom P` sends homotopic morphisms to
homotopic morphisms. -/
noncomputable def internalHomMap {Y' : CochainComplex C ℤ} {k k' : Y ⟶ Y'} (h : Homotopy k k') :
    Homotopy ((CochainComplex.internalHom P).map k) ((CochainComplex.internalHom P).map k') :=
  (h.compLeft _).internalHomEquiv

end Homotopy
