import Langlands.Representation.Archimedean.TwoBlockEnvelopingProjection
import Langlands.Algebra.TensorProductCenter
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Finiteness of the two-block Levi center over the ambient center -/

noncomputable section

open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.TwoBlockEnveloping

open VermaPBW Kostant MvPolynomial
open Langlands.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (a b : ℕ)

local notation "M" => fun k : ℕ => Matrix (Fin k) (Fin k) ℂ
local notation "U" => VermaGL.glU
local notation "Z" => VermaGL.center
local notation "P" => fun k : ℕ => MvPolynomial (Fin k) ℂ
local notation "L" => blockLevi (a + b) a
local notation "UL" => UniversalEnvelopingAlgebra ℂ L
local notation "ZL" => Subalgebra.center ℂ UL
local notation "e" => (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))

/-- Insert two complex matrices in the diagonal blocks. -/
def blockDiagonalComplexMatrixMap : (M a × M b) →ₗ[ℂ] M (a + b) where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2)
  map_add' p q := by
    change Matrix.reindexLinearEquiv ℂ _ e e (Matrix.fromBlocks (p.1 + q.1) 0 0 (p.2 + q.2)) =
      Matrix.reindexLinearEquiv ℂ _ e e (Matrix.fromBlocks p.1 0 0 p.2) +
        Matrix.reindexLinearEquiv ℂ _ e e (Matrix.fromBlocks q.1 0 0 q.2)
    rw [← map_add, Matrix.fromBlocks_add, zero_add, zero_add]
  map_smul' k p := by
    change Matrix.reindexLinearEquiv ℂ _ e e (Matrix.fromBlocks (k • p.1) 0 0 (k • p.2)) =
      k • Matrix.reindexLinearEquiv ℂ _ e e (Matrix.fromBlocks p.1 0 0 p.2)
    rw [← map_smul, Matrix.fromBlocks_smul, smul_zero, smul_zero]

theorem blockDiagonalComplexMatrixMap_apply (p : M a × M b) :
    blockDiagonalComplexMatrixMap a b p = Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2) :=
  rfl

private theorem blockDiagonalComplexMatrixMap_mul (p q : M a × M b) :
    blockDiagonalComplexMatrixMap a b (p * q) =
      blockDiagonalComplexMatrixMap a b p * blockDiagonalComplexMatrixMap a b q := by
  change Matrix.reindexAlgEquiv ℂ _ e (Matrix.fromBlocks (p.1 * q.1) 0 0 (p.2 * q.2)) =
    Matrix.reindexAlgEquiv ℂ _ e (Matrix.fromBlocks p.1 0 0 p.2) *
      Matrix.reindexAlgEquiv ℂ _ e (Matrix.fromBlocks q.1 0 0 q.2)
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem val_left_lt (i : Fin a) : (e (Sum.inl i)).val < a := by
  simpa only [finSumFinEquiv_apply_left, Fin.val_castAdd] using i.isLt

private theorem val_right_le (i : Fin b) : a ≤ (e (Sum.inr i)).val := by
  rw [finSumFinEquiv_apply_right, Fin.val_natAdd]
  exact Nat.le_add_right _ _

private theorem blockDiagonalComplexMatrixMap_mem (p : M a × M b) :
    blockDiagonalComplexMatrixMap a b p ∈ L := by
  intro i j hij
  obtain ⟨i, rfl⟩ := (e).surjective i
  obtain ⟨j, rfl⟩ := (e).surjective j
  rw [blockDiagonalComplexMatrixMap_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact False.elim (hij (by simp [blockLetterWeight, blockDiagonalGrade]))
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j => exact False.elim (hij (by simp [blockLetterWeight, blockDiagonalGrade]))

/-- The two complex matrix Lie algebras identify with the block diagonal Levi. -/
def blockLeviLieEquiv : (M a × M b) ≃ₗ⁅ℂ⁆ L where
  toFun p := ⟨blockDiagonalComplexMatrixMap a b p, blockDiagonalComplexMatrixMap_mem a b p⟩
  invFun x := (Matrix.toBlocks₁₁ (Matrix.reindex (e).symm (e).symm x.val),
    Matrix.toBlocks₂₂ (Matrix.reindex (e).symm (e).symm x.val))
  map_add' x y := Subtype.ext (map_add (blockDiagonalComplexMatrixMap a b) x y)
  map_smul' k x := Subtype.ext (map_smul (blockDiagonalComplexMatrixMap a b) k x)
  left_inv p := by
    apply Prod.ext
    · ext i j
      change (Matrix.fromBlocks p.1 0 0 p.2) ((e).symm (e (Sum.inl i)))
        ((e).symm (e (Sum.inl j))) = p.1 i j
      simp
    · ext i j
      change (Matrix.fromBlocks p.1 0 0 p.2) ((e).symm (e (Sum.inr i)))
        ((e).symm (e (Sum.inr j))) = p.2 i j
      simp
  right_inv x := by
    apply Subtype.ext
    ext i j
    obtain ⟨i, rfl⟩ := (e).surjective i
    obtain ⟨j, rfl⟩ := (e).surjective j
    let A := Matrix.reindex (e).symm (e).symm x.val
    change Matrix.reindex e e (Matrix.fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂)
      (e i) (e j) = x.val (e i) (e j)
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j =>
        symm
        apply x.property
        change blockLetterWeight (a + b) a (e (Sum.inl i), e (Sum.inr j)) ≠ 0
        rw [(blockLetterWeight_eq_one_iff (a + b) a _ _).mpr
          ⟨val_left_lt a b i, val_right_le a b j⟩]
        exact one_ne_zero
    | inr i =>
      cases j with
      | inl j =>
        symm
        apply x.property
        change blockLetterWeight (a + b) a (e (Sum.inr i), e (Sum.inl j)) ≠ 0
        rw [(blockLetterWeight_eq_neg_one_iff (a + b) a _ _).mpr
          ⟨val_right_le a b i, val_left_lt a b j⟩]
        exact neg_ne_zero.mpr one_ne_zero
      | inr j => rfl
  map_lie' {p q} := by
    apply Subtype.ext
    change blockDiagonalComplexMatrixMap a b (p * q - q * p) =
      blockDiagonalComplexMatrixMap a b p * blockDiagonalComplexMatrixMap a b q -
        blockDiagonalComplexMatrixMap a b q * blockDiagonalComplexMatrixMap a b p
    rw [map_sub, blockDiagonalComplexMatrixMap_mul, blockDiagonalComplexMatrixMap_mul]

theorem blockLeviLieEquiv_apply (p : M a × M b) :
    (blockLeviLieEquiv a b p).val = blockDiagonalComplexMatrixMap a b p := rfl

/-- The enveloping algebra of the Levi, written as a tensor product. -/
def blockLeviTensorEquiv : UL ≃ₐ[ℂ] U a ⊗[ℂ] U b :=
  (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b).symm).trans
    (LieEnvelopingEquiv.envelopingProduct ℂ (M a) (M b))

/-- The Levi center, written as a tensor product of the two block centers. -/
def blockLeviCenterTensorEquiv : ZL ≃ₐ[ℂ] (Z a ⊗[ℂ] Z b) :=
  (LieEnvelopingEquiv.center (blockLeviTensorEquiv a b)).trans
    (tensorProductCenter ℂ (U a) (U b)).symm

/-- Lie inclusion of the first complex matrix block. -/
def firstComplexMatrixBlockInclusion : M a →ₗ⁅ℂ⁆ M (a + b) :=
  (L).incl.comp ((blockLeviLieEquiv a b).toLieHom.comp (LieHom.inl ℂ (M a) (M b)))

/-- Lie inclusion of the second complex matrix block. -/
def secondComplexMatrixBlockInclusion : M b →ₗ⁅ℂ⁆ M (a + b) :=
  (L).incl.comp ((blockLeviLieEquiv a b).toLieHom.comp (LieHom.inr ℂ (M a) (M b)))

/-- Enveloping inclusion of the first complex matrix block. -/
def firstComplexMatrixBlockEnveloping : U a →ₐ[ℂ] U (a + b) :=
  LieEnvelopingEquiv.map (firstComplexMatrixBlockInclusion a b)

/-- Enveloping inclusion of the second complex matrix block. -/
def secondComplexMatrixBlockEnveloping : U b →ₐ[ℂ] U (a + b) :=
  LieEnvelopingEquiv.map (secondComplexMatrixBlockInclusion a b)

private theorem firstComplexMatrixBlockInclusion_unit (i j : Fin a) :
    firstComplexMatrixBlockInclusion a b (unitE a (i, j)) =
      unitE (a + b) (Fin.castAdd b i, Fin.castAdd b j) := by
  change Matrix.reindex e e (Matrix.fromBlocks (unitE a (i, j)) 0 0 0) = _
  have h : Matrix.fromBlocks (unitE a (i, j)) (0 : Matrix (Fin a) (Fin b) ℂ)
      (0 : Matrix (Fin b) (Fin a) ℂ) (0 : M b) =
        Matrix.single (Sum.inl i) (Sum.inl j) 1 := by
    ext x y
    cases x <;> cases y <;> simp [unitE, Matrix.single_apply]
  rw [h, Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_left, unitE]

private theorem secondComplexMatrixBlockInclusion_unit (i j : Fin b) :
    secondComplexMatrixBlockInclusion a b (unitE b (i, j)) =
      unitE (a + b) (Fin.natAdd a i, Fin.natAdd a j) := by
  change Matrix.reindex e e (Matrix.fromBlocks 0 0 0 (unitE b (i, j))) = _
  have h : Matrix.fromBlocks (0 : M a) (0 : Matrix (Fin a) (Fin b) ℂ)
      0 (unitE b (i, j)) = Matrix.single (Sum.inr i) (Sum.inr j) 1 := by
    ext x y
    cases x <;> cases y <;> simp [unitE, Matrix.single_apply]
  rw [h, Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_right, unitE]

private theorem blockLeviTensorEquiv_symm_tmul (x : U a) (y : U b) :
    leviInclusion (a + b) a ((blockLeviTensorEquiv a b).symm (x ⊗ₜ[ℂ] y)) =
      firstComplexMatrixBlockEnveloping a b x * secondComplexMatrixBlockEnveloping a b y := by
  change leviInclusion (a + b) a
    ((LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b))
      ((LieEnvelopingEquiv.envelopingProduct ℂ (M a) (M b)).symm (x ⊗ₜ[ℂ] y))) = _
  rw [LieEnvelopingEquiv.envelopingProduct_symm_tmul, map_mul, map_mul]
  have hl :
      ((leviInclusion (a + b) a).comp
        (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)).toAlgHom).comp
        (LieEnvelopingEquiv.map (LieHom.inl ℂ (M a) (M b))) =
        firstComplexMatrixBlockEnveloping a b := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change leviInclusion (a + b) a
      (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)
        (LieEnvelopingEquiv.map (LieHom.inl ℂ (M a) (M b)) (UniversalEnvelopingAlgebra.ι ℂ X))) =
      LieEnvelopingEquiv.map (firstComplexMatrixBlockInclusion a b)
        (UniversalEnvelopingAlgebra.ι ℂ X)
    rw [LieEnvelopingEquiv.map_generator, LieEnvelopingEquiv.enveloping_generator,
      leviInclusion_ι, LieEnvelopingEquiv.map_generator]
    rfl
  have hr :
      ((leviInclusion (a + b) a).comp
        (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)).toAlgHom).comp
        (LieEnvelopingEquiv.map (LieHom.inr ℂ (M a) (M b))) =
        secondComplexMatrixBlockEnveloping a b := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro Y
    change leviInclusion (a + b) a
      (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)
        (LieEnvelopingEquiv.map (LieHom.inr ℂ (M a) (M b)) (UniversalEnvelopingAlgebra.ι ℂ Y))) =
      LieEnvelopingEquiv.map (secondComplexMatrixBlockInclusion a b)
        (UniversalEnvelopingAlgebra.ι ℂ Y)
    rw [LieEnvelopingEquiv.map_generator, LieEnvelopingEquiv.enveloping_generator,
      leviInclusion_ι, LieEnvelopingEquiv.map_generator]
    rfl
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hl x) (DFunLike.congr_fun hr y)

private theorem first_second_block_commute (x : U a) (y : U b) :
    Commute (firstComplexMatrixBlockEnveloping a b x) (secondComplexMatrixBlockEnveloping a b y) :=
  by
    have h : Commute (x ⊗ₜ[ℂ] (1 : U b)) ((1 : U a) ⊗ₜ[ℂ] y) := by
      show (x ⊗ₜ[ℂ] (1 : U b)) * ((1 : U a) ⊗ₜ[ℂ] y) =
        ((1 : U a) ⊗ₜ[ℂ] y) * (x ⊗ₜ[ℂ] (1 : U b))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have he := h.map ((leviInclusion (a + b) a).comp (blockLeviTensorEquiv a b).symm.toAlgHom)
    change Commute
      (leviInclusion (a + b) a ((blockLeviTensorEquiv a b).symm (x ⊗ₜ[ℂ] 1)))
      (leviInclusion (a + b) a ((blockLeviTensorEquiv a b).symm (1 ⊗ₜ[ℂ] y))) at he
    simpa only [blockLeviTensorEquiv_symm_tmul, map_one, mul_one, one_mul] using he

private theorem map_W_of_unit {k n : ℕ} (f : U k →ₐ[ℂ] U n) (j : Fin k → Fin n)
    (hj : ∀ i i', f (VermaGL.unitU k i i') = VermaGL.unitU n (j i) (j i'))
    (w : List (Idx k)) : f (W k w) = W n (w.map (Prod.map j j)) := by
  induction w with
  | nil => simp only [List.map_nil, W_nil, map_one]
  | cons c w ih =>
    rw [List.map_cons, W_cons, W_cons, map_mul, ih]
    exact congrArg (· * _) (hj c.1 c.2)

private theorem firstBlock_map_W (w : List (Idx a)) :
    firstComplexMatrixBlockEnveloping a b (W a w) =
      W (a + b) (w.map (Prod.map (Fin.castAdd b) (Fin.castAdd b))) :=
  map_W_of_unit _ _ (fun i j =>
    (LieEnvelopingEquiv.map_generator _ (unitE a (i, j))).trans
      (congrArg (UniversalEnvelopingAlgebra.ι ℂ) (firstComplexMatrixBlockInclusion_unit a b i j))) w

private theorem secondBlock_map_W (w : List (Idx b)) :
    secondComplexMatrixBlockEnveloping a b (W b w) =
      W (a + b) (w.map (Prod.map (Fin.natAdd a) (Fin.natAdd a))) :=
  map_W_of_unit _ _ (fun i j =>
    (LieEnvelopingEquiv.map_generator _ (unitE b (i, j))).trans
      (congrArg (UniversalEnvelopingAlgebra.ι ℂ) (secondComplexMatrixBlockInclusion_unit a b i j))) w

private theorem Psi_W_upper_mul {n : ℕ} (lam : Fin n → ℂ)
    (w : List (Idx n)) (hw : ∀ c ∈ w, c.1 < c.2) (v : U n) :
    Psi n (vVal n lam 0) (W n w * v) =
      (w.map (vVal n lam 0)).prod * Psi n (vVal n lam 0) v := by
  induction w with
  | nil => simp only [W_nil, one_mul, List.map_nil, List.prod_nil]
  | cons c w ih =>
    rw [W_cons, mul_assoc, Psi_unitE_up_mul n lam 0 ⟨c, hw c List.mem_cons_self⟩,
      ih (fun c hc => hw c (List.mem_cons_of_mem _ hc)), List.map_cons, List.prod_cons, mul_assoc]

private theorem Psi_mul_W_lower {n : ℕ} (lam : Fin n → ℂ)
    (w : List (Idx n)) (hw : ∀ c ∈ w, ¬ c.1 < c.2) (v : U n) :
    Psi n (vVal n lam 0) (v * W n w) =
      Psi n (vVal n lam 0) v * (w.map (vVal n lam 0)).prod := by
  induction w generalizing v with
  | nil => simp only [W_nil, mul_one, List.map_nil, List.prod_nil]
  | cons c w ih =>
    rw [W_cons, ← mul_assoc, ih (fun c hc => hw c (List.mem_cons_of_mem _ hc)),
      Psi_mul_unitE_lo n lam 0 ⟨c, hw c List.mem_cons_self⟩, List.map_cons, List.prod_cons]
    ring

private theorem vVal_zero {n : ℕ} (lam : Fin n → ℂ) (c : Idx n) :
    vVal n lam 0 c = if c.1 = c.2 then lam c.1 else 0 := by
  unfold vVal
  split_ifs with hlt heq heq
  · exact (hlt.ne heq).elim
  · simp [supCoeff]
  · rfl
  · rfl

private theorem vVal_map_prod {k n : ℕ} (lam : Fin n → ℂ) (j : Fin k → Fin n)
    (hj : Function.Injective j) (w : List (Idx k)) :
    (((w.map (Prod.map j j)).map (vVal n lam 0))).prod =
      (w.map (vVal k (lam ∘ j) 0)).prod := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, vVal_zero, Prod.map_fst, Prod.map_snd, hj.eq_iff]

private theorem upperWord_lt {k n : ℕ} (j : Fin k → Fin n) (hj : StrictMono j) (α : Idx k →₀ ℕ)
    (c : Idx n) (hc : c ∈ (expand ((upList k).map Subtype.val) α).map (Prod.map j j)) :
    c.1 < c.2 := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp (mem_expand hc')
  exact hj d.property

private theorem lowerWord_not_lt {k n : ℕ} (j : Fin k → Fin n) (hj : StrictMono j)
    (α : Idx k →₀ ℕ) (c : Idx n)
    (hc : c ∈ (expand ((loList k).map Subtype.val) α).map (Prod.map j j)) : ¬ c.1 < c.2 := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp (mem_expand hc')
  exact fun h => d.property (hj.lt_iff_lt.mp h)

private theorem eval_gam_block_basis (lam : Fin (a + b) → ℂ)
    (α : Idx a →₀ ℕ) (β : Idx b →₀ ℕ) :
    eval lam (VermaCentral.gam (a + b)
      (firstComplexMatrixBlockEnveloping a b (basisU a α) *
        secondComplexMatrixBlockEnveloping a b (basisU b β))) =
      eval (lam ∘ Fin.castAdd b) (VermaCentral.gam a (basisU a α)) *
        eval (lam ∘ Fin.natAdd a) (VermaCentral.gam b (basisU b β)) := by
  let u₁ := expand ((upList a).map Subtype.val) α
  let l₁ := expand ((loList a).map Subtype.val) α
  let u₂ := expand ((upList b).map Subtype.val) β
  let l₂ := expand ((loList b).map Subtype.val) β
  let f := firstComplexMatrixBlockEnveloping a b
  let g := secondComplexMatrixBlockEnveloping a b
  simp only [VermaCentral.eval_gam]
  rw [Psi_basisU, Psi_basisU, wt, wt, bsList, bsList, expand_append, expand_append,
    List.map_append, List.map_append, List.prod_append, List.prod_append]
  rw [basisU_apply_split, basisU_apply_split, map_mul f, map_mul g]
  change Psi (a + b) (vVal (a + b) lam 0)
      ((f (W a u₁) * f (W a l₁)) * (g (W b u₂) * g (W b l₂))) = _
  have he : (f (W a u₁) * f (W a l₁)) * (g (W b u₂) * g (W b l₂)) =
      f (W a u₁) * (g (W b u₂) * ((f (W a l₁)) * g (W b l₂))) := by
    calc
      _ = f (W a u₁) * ((f (W a l₁) * g (W b u₂)) * g (W b l₂)) := by
        simp only [mul_assoc]
      _ = _ := by rw [(first_second_block_commute a b (W a l₁) (W b u₂)).eq, mul_assoc]
  rw [he]
  simp only [f, g, firstBlock_map_W, secondBlock_map_W]
  have hj : StrictMono (Fin.castAdd b : Fin a → Fin (a + b)) := fun _ _ h => h
  have hk : StrictMono (Fin.natAdd a : Fin b → Fin (a + b)) :=
    fun _ _ h => Nat.add_lt_add_left h a
  rw [Psi_W_upper_mul lam _ (upperWord_lt _ hj α),
    Psi_W_upper_mul lam _ (upperWord_lt _ hk β),
    Psi_mul_W_lower lam _ (lowerWord_not_lt _ hk β),
    ← one_mul (W (a + b) (l₁.map (Prod.map (Fin.castAdd b) (Fin.castAdd b)))),
    Psi_mul_W_lower lam _ (lowerWord_not_lt _ hj α), Psi_one, one_mul]
  rw [vVal_map_prod lam _ hj.injective, vVal_map_prod lam _ hk.injective,
    vVal_map_prod lam _ hj.injective, vVal_map_prod lam _ hk.injective]
  ring

private theorem eval_gam_block_tmul (lam : Fin (a + b) → ℂ) (x : U a) (y : U b) :
    eval lam (VermaCentral.gam (a + b)
      (leviInclusion (a + b) a ((blockLeviTensorEquiv a b).symm (x ⊗ₜ[ℂ] y)))) =
      eval (lam ∘ Fin.castAdd b) (VermaCentral.gam a x) *
        eval (lam ∘ Fin.natAdd a) (VermaCentral.gam b y) := by
  let f := (aeval lam).toLinearMap ∘ₗ VermaCentral.gam (a + b) ∘ₗ
    (leviInclusion (a + b) a).toLinearMap ∘ₗ (blockLeviTensorEquiv a b).symm.toLinearEquiv.toLinearMap
  let ga := (aeval (lam ∘ Fin.castAdd b)).toLinearMap ∘ₗ VermaCentral.gam a
  let gb := (aeval (lam ∘ Fin.natAdd a)).toLinearMap ∘ₗ VermaCentral.gam b
  let g := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ga gb)
  have he : f = g := by
    apply ((basisU a).tensorProduct (basisU b)).ext
    rintro ⟨α, β⟩
    simp only [Module.Basis.tensorProduct_apply, f, g, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply, LinearEquiv.coe_coe, aeval_eq_eval,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply', ga, gb]
    rw [blockLeviTensorEquiv_symm_tmul]
    exact eval_gam_block_basis a b lam α β
  have h := LinearMap.congr_fun he (x ⊗ₜ[ℂ] y)
  simpa only [f, g, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply,
    LinearEquiv.coe_coe, aeval_eq_eval, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', ga, gb] using h

/-- Tensor product of the block polynomial algebras, in ambient diagonal coordinates. -/
def blockPolynomialTensorEquiv : P a ⊗[ℂ] P b ≃ₐ[ℂ] P (a + b) :=
  (MvPolynomial.tensorEquivSum ℂ (Fin a) (Fin b) ℂ).trans (MvPolynomial.renameEquiv ℂ e)

private theorem blockPolynomialTensorEquiv_tmul (p : P a) (q : P b) :
    blockPolynomialTensorEquiv a b (p ⊗ₜ[ℂ] q) =
      rename (Fin.castAdd b) p * rename (Fin.natAdd a) q := by
  let E := (blockPolynomialTensorEquiv a b).toAlgHom
  let l : P a →ₐ[ℂ] P a ⊗[ℂ] P b := Algebra.TensorProduct.includeLeft
  let r : P b →ₐ[ℂ] P a ⊗[ℂ] P b := Algebra.TensorProduct.includeRight
  have hl : E.comp l = rename (Fin.castAdd b) := by
    apply MvPolynomial.algHom_ext
    intro i
    change blockPolynomialTensorEquiv a b (X i ⊗ₜ[ℂ] 1) = rename (Fin.castAdd b) (X i)
    simp [blockPolynomialTensorEquiv]
  have hr : E.comp r = rename (Fin.natAdd a) := by
    apply MvPolynomial.algHom_ext
    intro i
    change blockPolynomialTensorEquiv a b (1 ⊗ₜ[ℂ] X i) = rename (Fin.natAdd a) (X i)
    simp [blockPolynomialTensorEquiv]
  have h : l p * r q = p ⊗ₜ[ℂ] q := by
    change (p ⊗ₜ[ℂ] (1 : P b)) * ((1 : P a) ⊗ₜ[ℂ] q) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change E (p ⊗ₜ[ℂ] q) = _
  rw [← h, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hl p) (DFunLike.congr_fun hr q)

/-- The product Harish-Chandra map on the Levi center, in ambient diagonal coordinates. -/
def blockLeviCenterPolynomial : ZL →ₐ[ℂ] P (a + b) :=
  (blockPolynomialTensorEquiv a b).toAlgHom.comp
    ((Algebra.TensorProduct.map (VermaCentral.gamC a) (VermaCentral.gamC b)).comp
      (blockLeviCenterTensorEquiv a b).toAlgHom)

theorem blockLeviCenterPolynomial_injective : Function.Injective (blockLeviCenterPolynomial a b) :=
  (blockPolynomialTensorEquiv a b).injective.comp
    ((TensorProduct.map_injective_of_flat_flat (VermaCentral.gamC a).toLinearMap
      (VermaCentral.gamC b).toLinearMap (VermaCentral.gamC_injective a)
      (VermaCentral.gamC_injective b)).comp (blockLeviCenterTensorEquiv a b).injective)

private theorem blockLeviCenterTensorEquiv_symm_tmul (z : Z a) (w : Z b) :
    ((blockLeviCenterTensorEquiv a b).symm (z ⊗ₜ[ℂ] w)).val =
      (blockLeviTensorEquiv a b).symm (z.val ⊗ₜ[ℂ] w.val) := by
  change ((LieEnvelopingEquiv.center (blockLeviTensorEquiv a b)).symm
    (tensorProductCenter ℂ (U a) (U b) (z ⊗ₜ[ℂ] w))).val = _
  apply (blockLeviTensorEquiv a b).injective
  rw [AlgEquiv.apply_symm_apply, ← LieEnvelopingEquiv.center_apply]
  simp only [AlgEquiv.apply_symm_apply, tensorProductCenter_tmul]

theorem blockLeviCenterPolynomial_eq_gam (z : ZL) :
    blockLeviCenterPolynomial a b z = VermaCentral.gam (a + b) (leviInclusion (a + b) a z.val) := by
  let f := (blockLeviCenterPolynomial a b).toLinearMap ∘ₗ
    (blockLeviCenterTensorEquiv a b).symm.toLinearEquiv.toLinearMap
  let g := VermaCentral.gam (a + b) ∘ₗ (leviInclusion (a + b) a).toLinearMap ∘ₗ
    (Subalgebra.center ℂ UL).val.toLinearMap ∘ₗ
    (blockLeviCenterTensorEquiv a b).symm.toLinearEquiv.toLinearMap
  have h : f = g := by
    apply TensorProduct.ext'
    intro x y
    change blockLeviCenterPolynomial a b ((blockLeviCenterTensorEquiv a b).symm (x ⊗ₜ[ℂ] y)) =
      VermaCentral.gam (a + b) (leviInclusion (a + b) a
        ((blockLeviCenterTensorEquiv a b).symm (x ⊗ₜ[ℂ] y)).val)
    rw [blockLeviCenterTensorEquiv_symm_tmul, blockLeviCenterPolynomial,
      AlgHom.comp_apply, AlgHom.comp_apply]
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul,
      blockPolynomialTensorEquiv_tmul]
    refine MvPolynomial.funext fun lam => ?_
    rw [map_mul, eval_rename, eval_rename, eval_gam_block_tmul]
    rfl
  have h' := LinearMap.congr_fun h (blockLeviCenterTensorEquiv a b z)
  change blockLeviCenterPolynomial a b
      ((blockLeviCenterTensorEquiv a b).symm (blockLeviCenterTensorEquiv a b z)) =
    VermaCentral.gam (a + b) (leviInclusion (a + b) a
      ((blockLeviCenterTensorEquiv a b).symm (blockLeviCenterTensorEquiv a b z)).val) at h'
  simpa only [AlgEquiv.symm_apply_apply] using h'

theorem blockLeviCenterPolynomial_comp :
    (blockLeviCenterPolynomial a b).comp (blockLeviCenterProjection (a + b) a) =
      VermaCentral.gamC (a + b) := by
  apply AlgHom.ext
  intro z
  rw [AlgHom.comp_apply, blockLeviCenterPolynomial_eq_gam, VermaCentral.gamC_apply]
  have h := gam_eq_zero_of_mem_upperRadicalRightSpan (a + b) a
    (sub_leviInclusion_centerProjection_mem_upperSpan (a + b) a z)
  exact (sub_eq_zero.mp (by simpa only [map_sub] using h)).symm

set_option maxHeartbeats 1000000 in
private theorem gamC_finite (n : ℕ) : (VermaCentral.gamC n).Finite := by
  have h₁ : (VermaCentral.gamC n).rangeRestrict.Finite :=
    AlgHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _)
  have h₂ : (VermaCentral.imA n).val.Finite := VermaCentral.finite_imA n
  have h₃ : ((VermaCentral.imA n).val.comp (VermaCentral.gamC n).rangeRestrict).Finite :=
    h₂.comp h₁
  have h₄ : (VermaCentral.imA n).val.comp (VermaCentral.gamC n).rangeRestrict =
      VermaCentral.gamC n := AlgHom.ext fun _ => rfl
  exact h₄ ▸ h₃

private theorem center_isNoetherian (n : ℕ) : IsNoetherianRing (Z n) := by
  let A := VermaCentral.imA n
  have h : (⊤ : Subalgebra ℂ A).FG :=
    fg_of_fg_of_fg ℂ A (P n)
      Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective
  have : Algebra.FiniteType ℂ A := ⟨h⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  exact isNoetherianRing_of_ringEquiv A
    (AlgEquiv.ofInjective (VermaCentral.gamC n) (VermaCentral.gamC_injective n)).symm.toRingEquiv

/-- The parabolic center homomorphism is module-finite. -/
theorem blockLeviCenterProjection_finite : (blockLeviCenterProjection (a + b) a).Finite := by
  let f := blockLeviCenterProjection (a + b) a
  let g := blockLeviCenterPolynomial a b
  have hfg : (g.comp f).Finite := blockLeviCenterPolynomial_comp a b ▸ gamC_finite (a + b)
  let : Algebra (Z (a + b)) ZL := f.toRingHom.toAlgebra
  let : Algebra ZL (P (a + b)) := g.toRingHom.toAlgebra
  let : Algebra (Z (a + b)) (P (a + b)) := (g.comp f).toRingHom.toAlgebra
  have : IsScalarTower (Z (a + b)) ZL (P (a + b)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsNoetherianRing (Z (a + b)) := center_isNoetherian (a + b)
  have : Module.Finite (Z (a + b)) (P (a + b)) := hfg
  change Module.Finite (Z (a + b)) ZL
  exact Module.Finite.of_injective (IsScalarTower.toAlgHom (Z (a + b)) ZL (P (a + b))).toLinearMap
    (blockLeviCenterPolynomial_injective a b)

end Langlands.Archimedean.TwoBlockEnveloping
