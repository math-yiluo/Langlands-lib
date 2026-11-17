import Langlands.Representation.Archimedean.RealGramFunction
import Langlands.Representation.Archimedean.RealBlockRotation

/-!
# The block polynomial of a real standard module

For a list `ds` of real blocks this module defines a polynomial `blockPoly n ds 0` in the
entries `X_{ij}` of an `n × n` matrix:

* a real character block of parity `ε` at position `q` contributes `X_{qq}^ε`;
* a real induction block of weight `m` at the positions `q, q + 1` contributes
  `Φ_q = ℓ₊^N + (-1)^N ℓ₋^N` with `N = |m| + 1`, where
  `ℓ₊ = X_{qq} + X_{q+1,q+1} + i (X_{q,q+1} - X_{q+1,q})` and
  `ℓ₋ = X_{q+1,q+1} - X_{qq} - i (X_{q,q+1} + X_{q+1,q})`.

It proves the three algebraic facts used to build a nonzero `O(n)`-finite function of the real
standard module:

* the value at the identity matrix is nonzero (`eval_one_blockPoly_ne_zero`);
* the sign parity of the position characters (`hasSignParity_blockPoly`);
* at an induction block, the polynomial is `Φ_q · R` with `R` free of the rows `q, q + 1`
  (`exists_blockPoly_eq_blockFactor_mul`), and rotating the rows `q, q + 1` by `(u, v)`
  multiplies `ℓ₊` by `u - iv` and `ℓ₋` by `u + iv` (`eval_rotated_blockFactor_mul`).
-/

noncomputable section

open Matrix

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean GramFormula RealGramFunction RealBlockRotation

namespace RealStandardNontrivial

set_option autoImplicit false

variable {n : ℕ}

/-! ## Variables at natural-number indices -/

/-- The variable `X_{ij}` at natural-number indices, `0` outside the range. -/
def var (n i j : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  if h : i < n ∧ j < n then MvPolynomial.X (⟨i, h.1⟩, ⟨j, h.2⟩) else 0

@[simp]
theorem eval_var_fin (Y : Fin n × Fin n → ℂ) (i j : Fin n) :
    MvPolynomial.eval Y (var n i j) = Y (i, j) := by
  simp [var]

/-- `ℓ₊ = X_{qq} + X_{q+1,q+1} + i (X_{q,q+1} - X_{q+1,q})`. -/
def lplus (n q : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  var n q q + var n (q + 1) (q + 1) +
    MvPolynomial.C Complex.I * (var n q (q + 1) - var n (q + 1) q)

/-- `ℓ₋ = X_{q+1,q+1} - X_{qq} - i (X_{q,q+1} + X_{q+1,q})`. -/
def lminus (n q : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  var n (q + 1) (q + 1) - var n q q -
    MvPolynomial.C Complex.I * (var n q (q + 1) + var n (q + 1) q)

/-- The factor `Φ_q = ℓ₊^N + (-1)^N ℓ₋^N` of an induction block at the positions `q, q + 1`. -/
def blockFactor (n q N : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  lplus n q ^ N + MvPolynomial.C ((-1 : ℂ) ^ N) * lminus n q ^ N

/-- The block polynomial of the list `ds` whose first position is `q`. -/
def blockPoly (n : ℕ) : List RealBlock → ℕ → MvPolynomial (Fin n × Fin n) ℂ
  | [], _ => 1
  | .character d :: ds, q => var n q q ^ d.parity.val * blockPoly n ds (q + 1)
  | .induced d :: ds, q => blockFactor n q (d.weight.natAbs + 1) * blockPoly n ds (q + 2)

theorem eval_lplus {q : ℕ} (h : q + 1 < n) (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval Y (lplus n q) =
      Y (ia h, ia h) + Y (ib h, ib h) + Complex.I * (Y (ia h, ib h) - Y (ib h, ia h)) := by
  change MvPolynomial.eval Y (var n (ia h) (ia h) + var n (ib h) (ib h) +
    MvPolynomial.C Complex.I * (var n (ia h) (ib h) - var n (ib h) (ia h))) = _
  simp only [map_add, map_mul, map_sub, MvPolynomial.eval_C, eval_var_fin]

theorem eval_lminus {q : ℕ} (h : q + 1 < n) (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval Y (lminus n q) =
      Y (ib h, ib h) - Y (ia h, ia h) - Complex.I * (Y (ia h, ib h) + Y (ib h, ia h)) := by
  change MvPolynomial.eval Y (var n (ib h) (ib h) - var n (ia h) (ia h) -
    MvPolynomial.C Complex.I * (var n (ia h) (ib h) + var n (ib h) (ia h))) = _
  simp only [map_add, map_mul, map_sub, MvPolynomial.eval_C, eval_var_fin]

theorem eval_blockFactor (n q N : ℕ) (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval Y (blockFactor n q N) =
      MvPolynomial.eval Y (lplus n q) ^ N +
        (-1 : ℂ) ^ N * MvPolynomial.eval Y (lminus n q) ^ N := by
  simp only [blockFactor, map_add, map_mul, map_pow, MvPolynomial.eval_C]

/-! ## The value at the identity -/

/-- The entries of the identity matrix. -/
def oneEntries (n : ℕ) : Fin n × Fin n → ℂ :=
  fun ij => (((1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)

theorem eval_blockFactor_one {q : ℕ} (h : q + 1 < n) {N : ℕ} (hN : N ≠ 0) :
    MvPolynomial.eval (oneEntries n) (blockFactor n q N) = 2 ^ N := by
  have hne := ia_ne_ib h
  rw [eval_blockFactor, eval_lplus h, eval_lminus h]
  simp only [oneEntries, Matrix.one_apply_eq, Matrix.one_apply_ne hne,
    Matrix.one_apply_ne hne.symm, Complex.ofReal_one, Complex.ofReal_zero]
  norm_num [zero_pow hN]

theorem eval_one_blockPoly_ne_zero : ∀ (ds : List RealBlock) (q : ℕ), q + realRank ds ≤ n →
    MvPolynomial.eval (oneEntries n) (blockPoly n ds q) ≠ 0
  | [], _, _ => by simp [blockPoly]
  | .character d :: ds, q, hq => by
      rw [realRank_cons] at hq
      simp only [RealBlock.rank] at hq
      have hv : MvPolynomial.eval (oneEntries n) (var n q q) = 1 := by
        have := eval_var_fin (oneEntries n) ⟨q, by omega⟩ ⟨q, by omega⟩
        rw [this]
        simp [oneEntries]
      rw [blockPoly, map_mul, map_pow, hv, one_pow, one_mul]
      exact eval_one_blockPoly_ne_zero ds (q + 1) (by omega)
  | .induced d :: ds, q, hq => by
      rw [realRank_cons] at hq
      simp only [RealBlock.rank] at hq
      rw [blockPoly, map_mul, eval_blockFactor_one (by omega : q + 1 < n) (Nat.succ_ne_zero _)]
      exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
        (eval_one_blockPoly_ne_zero ds (q + 2) (by omega))

/-! ## Sign parity -/

/-- The unit at a natural-number index, `1` outside the range. -/
def unitAt (a : Fin n → ℝˣ) (i : ℕ) : ℝˣ := if h : i < n then a ⟨i, h⟩ else 1

theorem unitAt_fin (a : Fin n → ℝˣ) (i : Fin n) : unitAt a i = a i := by
  simp [unitAt]

theorem signReal_eq_one_or (x : ℝ) : signReal x = 1 ∨ signReal x = -1 := by
  unfold signReal
  split_ifs <;> simp

theorem div_abs_eq_signReal (x : ℝˣ) : (x : ℝ) / |(x : ℝ)| = signReal x := by
  rw [div_eq_mul_inv, mul_inv_abs_eq_signReal x.ne_zero]

theorem character_signUnit (d : RealCharacterData) (x : ℝˣ) :
    (d.character (signUnit x) : ℂ) = ((signReal x : ℝ) : ℂ) ^ d.parity.val := by
  rw [d.character_eq, signUnit_div_abs, abs_signUnit, div_abs_eq_signReal]
  simp

theorem realInducedFirstCharacter_signUnit (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedFirstCharacter d (signUnit x) =
      ((signReal x : ℝ) : ℂ) ^ (d.weight.natAbs + 1) := by
  rw [realInducedFirstCharacter, signUnit_div_abs, abs_signUnit, div_abs_eq_signReal]
  simp

theorem realInducedSecondCharacter_signUnit (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedSecondCharacter d (signUnit x) = 1 := by
  rw [realInducedSecondCharacter, abs_signUnit]
  simp

/-- The entries with the rows multiplied by the signs of `a`. -/
def signedEntries (a : Fin n → ℝˣ) (Y : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun ij => ((signReal (a ij.1) : ℝ) : ℂ) * Y ij

theorem eval_signed_blockFactor {q : ℕ} (h : q + 1 < n) (N : ℕ) (a : Fin n → ℝˣ)
    (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (signedEntries a Y) (blockFactor n q N) =
      ((signReal (a (ia h)) : ℝ) : ℂ) ^ N * MvPolynomial.eval Y (blockFactor n q N) := by
  rw [eval_blockFactor, eval_blockFactor, eval_lplus h, eval_lminus h, eval_lplus h,
    eval_lminus h]
  simp only [signedEntries]
  set A := Y (ia h, ia h)
  set B := Y (ib h, ib h)
  set C := Y (ia h, ib h)
  set D := Y (ib h, ia h)
  have hNN : (-1 : ℂ) ^ N * (-1 : ℂ) ^ N = 1 := by rw [← mul_pow]; norm_num
  rcases signReal_eq_one_or (a (ia h)) with h1 | h1 <;>
    rcases signReal_eq_one_or (a (ib h)) with h2 | h2 <;> rw [h1, h2] <;> push_cast
  · ring
  · have e1 : 1 * A + -1 * B + Complex.I * (1 * C - -1 * D) = -(B - A - Complex.I * (C + D)) := by
      ring
    have e2 : -1 * B - 1 * A - Complex.I * (1 * C + -1 * D) = -(A + B + Complex.I * (C - D)) := by
      ring
    rw [e1, e2, neg_pow, neg_pow (A + B + Complex.I * (C - D))]
    linear_combination ((A + B + Complex.I * (C - D)) ^ N) * hNN
  · have e1 : -1 * A + 1 * B + Complex.I * (-1 * C - 1 * D) = (B - A - Complex.I * (C + D)) := by
      ring
    have e2 : 1 * B - -1 * A - Complex.I * (-1 * C + 1 * D) = (A + B + Complex.I * (C - D)) := by
      ring
    rw [e1, e2]
    linear_combination (-((B - A - Complex.I * (C + D)) ^ N)) * hNN
  · have e1 : -1 * A + -1 * B + Complex.I * (-1 * C - -1 * D) =
        -(A + B + Complex.I * (C - D)) := by ring
    have e2 : -1 * B - -1 * A - Complex.I * (-1 * C + -1 * D) =
        -(B - A - Complex.I * (C + D)) := by ring
    rw [e1, e2, neg_pow, neg_pow (B - A - Complex.I * (C + D))]
    ring

theorem eval_signed_blockPoly : ∀ (ds : List RealBlock) (q : ℕ), q + realRank ds ≤ n →
    ∀ (a : Fin n → ℝˣ) (Y : Fin n × Fin n → ℂ),
      MvPolynomial.eval (signedEntries a Y) (blockPoly n ds q) =
        (∏ l ∈ Finset.range (realRank ds),
          realPositionCharacter ds l (signUnit (unitAt a (q + l)))) *
          MvPolynomial.eval Y (blockPoly n ds q)
  | [], _, _, _, _ => by simp [blockPoly, realRank]
  | .character d :: ds, q, hq, a, Y => by
      rw [realRank_cons] at hq ⊢
      simp only [RealBlock.rank] at hq ⊢
      have hqn : q < n := by omega
      have hv : ∀ Z : Fin n × Fin n → ℂ,
          MvPolynomial.eval Z (var n q q) = Z (⟨q, hqn⟩, ⟨q, hqn⟩) := fun Z =>
        eval_var_fin Z ⟨q, hqn⟩ ⟨q, hqn⟩
      rw [add_comm 1, Finset.prod_range_succ']
      simp only [blockPoly, map_mul, map_pow, hv]
      rw [eval_signed_blockPoly ds (q + 1) (by omega) a Y]
      simp only [realPositionCharacter, add_zero]
      have hprod : (∏ l ∈ Finset.range (realRank ds),
          realPositionCharacter ds l (signUnit (unitAt a (q + (l + 1))))) =
          ∏ l ∈ Finset.range (realRank ds),
            realPositionCharacter ds l (signUnit (unitAt a (q + 1 + l))) :=
        Finset.prod_congr rfl fun l _ => by rw [show q + (l + 1) = q + 1 + l by omega]
      rw [hprod, character_signUnit, unitAt]
      simp only [hqn, dite_true, signedEntries]
      ring
  | .induced d :: ds, q, hq, a, Y => by
      rw [realRank_cons] at hq ⊢
      simp only [RealBlock.rank] at hq ⊢
      have h : q + 1 < n := by omega
      rw [add_comm 2, Finset.prod_range_succ', Finset.prod_range_succ']
      simp only [blockPoly, map_mul]
      rw [eval_signed_blockPoly ds (q + 2) (by omega) a Y, eval_signed_blockFactor h]
      simp only [realPositionCharacter, add_zero]
      have hprod : (∏ l ∈ Finset.range (realRank ds),
          realPositionCharacter ds l (signUnit (unitAt a (q + (l + 1 + 1))))) =
          ∏ l ∈ Finset.range (realRank ds),
            realPositionCharacter ds l (signUnit (unitAt a (q + 2 + l))) :=
        Finset.prod_congr rfl fun l _ => by rw [show q + (l + 1 + 1) = q + 2 + l by omega]
      rw [hprod, realInducedFirstCharacter_signUnit, realInducedSecondCharacter_signUnit]
      have hu : unitAt a q = a (ia h) := by simp [unitAt, ia, show q < n by omega]
      rw [hu]
      ring

/-- **Sign parity.** The block polynomial of `ds` has the sign parity of the position
characters of `ds`. -/
theorem hasSignParity_blockPoly (ds : List RealBlock) (hds : realRank ds = n) :
    HasSignParity (realPositionCharacter ds) (blockPoly n ds 0) := by
  intro a Y
  have h := eval_signed_blockPoly ds 0 (by omega) a Y
  simp only [zero_add] at h
  change MvPolynomial.eval (signedEntries a Y) (blockPoly n ds 0) = _
  rw [h]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun l => realPositionCharacter ds l (signUnit (unitAt a l))),
    hds]
  exact Finset.prod_congr rfl fun l _ => by rw [unitAt_fin]

/-! ## Dependence on rows -/

/-- `R` depends only on the rows whose indices lie in `S`. -/
def DependsOnRows (S : Set ℕ) (R : MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ Y Y' : Fin n × Fin n → ℂ, (∀ i j : Fin n, (i : ℕ) ∈ S → Y (i, j) = Y' (i, j)) →
    MvPolynomial.eval Y R = MvPolynomial.eval Y' R

theorem DependsOnRows.mono {S T : Set ℕ} (hST : S ⊆ T) {R : MvPolynomial (Fin n × Fin n) ℂ}
    (hR : DependsOnRows S R) : DependsOnRows T R :=
  fun Y Y' hY => hR Y Y' fun i j hi => hY i j (hST hi)

theorem dependsOnRows_C (S : Set ℕ) (c : ℂ) :
    DependsOnRows S (MvPolynomial.C c : MvPolynomial (Fin n × Fin n) ℂ) :=
  fun _ _ _ => by simp

theorem dependsOnRows_one (S : Set ℕ) : DependsOnRows S (1 : MvPolynomial (Fin n × Fin n) ℂ) :=
  fun _ _ _ => by simp

theorem DependsOnRows.add {S : Set ℕ} {R R' : MvPolynomial (Fin n × Fin n) ℂ}
    (hR : DependsOnRows S R) (hR' : DependsOnRows S R') : DependsOnRows S (R + R') :=
  fun Y Y' hY => by rw [map_add, map_add, hR Y Y' hY, hR' Y Y' hY]

theorem DependsOnRows.sub {S : Set ℕ} {R R' : MvPolynomial (Fin n × Fin n) ℂ}
    (hR : DependsOnRows S R) (hR' : DependsOnRows S R') : DependsOnRows S (R - R') :=
  fun Y Y' hY => by rw [map_sub, map_sub, hR Y Y' hY, hR' Y Y' hY]

theorem DependsOnRows.mul {S : Set ℕ} {R R' : MvPolynomial (Fin n × Fin n) ℂ}
    (hR : DependsOnRows S R) (hR' : DependsOnRows S R') : DependsOnRows S (R * R') :=
  fun Y Y' hY => by rw [map_mul, map_mul, hR Y Y' hY, hR' Y Y' hY]

theorem DependsOnRows.pow {S : Set ℕ} {R : MvPolynomial (Fin n × Fin n) ℂ}
    (hR : DependsOnRows S R) (N : ℕ) : DependsOnRows S (R ^ N) :=
  fun Y Y' hY => by rw [map_pow, map_pow, hR Y Y' hY]

theorem dependsOnRows_var (i j : ℕ) : DependsOnRows {i} (var n i j) := by
  intro Y Y' hY
  unfold var
  split_ifs with h
  · simp only [MvPolynomial.eval_X]
    exact hY ⟨i, h.1⟩ ⟨j, h.2⟩ rfl
  · simp

theorem dependsOnRows_blockFactor (q N : ℕ) :
    DependsOnRows {q, q + 1} (blockFactor n q N) := by
  have h1 : ∀ j, DependsOnRows {q, q + 1} (var n q j) := fun j =>
    (dependsOnRows_var q j).mono (by simp)
  have h2 : ∀ j, DependsOnRows {q, q + 1} (var n (q + 1) j) := fun j =>
    (dependsOnRows_var (q + 1) j).mono (by simp)
  refine ((((h1 q).add (h2 _)).add ((dependsOnRows_C _ _).mul ((h1 _).sub (h2 q)))).pow N).add
    ((dependsOnRows_C _ _).mul ((((h2 _).sub (h1 q)).sub
      ((dependsOnRows_C _ _).mul ((h1 _).add (h2 q)))).pow N))

theorem dependsOnRows_blockPoly : ∀ (ds : List RealBlock) (q : ℕ),
    DependsOnRows {l | q ≤ l} (blockPoly n ds q)
  | [], _ => dependsOnRows_one _
  | .character d :: ds, q => by
      rw [blockPoly]
      exact (((dependsOnRows_var q q).mono (by simp)).pow _).mul
        ((dependsOnRows_blockPoly ds (q + 1)).mono fun l (hl : q + 1 ≤ l) =>
          show q ≤ l by omega)
  | .induced d :: ds, q => by
      rw [blockPoly]
      refine ((dependsOnRows_blockFactor q _).mono ?_).mul
        ((dependsOnRows_blockPoly ds (q + 2)).mono fun l (hl : q + 2 ≤ l) =>
          show q ≤ l by omega)
      intro l hl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
      show q ≤ l
      omega

/-- **Factorization at an induction block.** If the induction block `d` of `ds` starts at `p`,
the block polynomial is `Φ_{q+p} · R` with `R` free of the rows `q + p, q + p + 1`. -/
theorem exists_blockPoly_eq_blockFactor_mul : ∀ (ds : List RealBlock) (q p : ℕ)
    (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
    ∃ R : MvPolynomial (Fin n × Fin n) ℂ,
      blockPoly n ds q = blockFactor n (q + p) (d.weight.natAbs + 1) * R ∧
        DependsOnRows {l | l ≠ q + p ∧ l ≠ q + p + 1} R
  | [], _, _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character d' :: ds, q, p + 1, d, h => by
      obtain ⟨R, hR, hfree⟩ := exists_blockPoly_eq_blockFactor_mul ds (q + 1) p d h
      refine ⟨var n q q ^ d'.parity.val * R, ?_, ?_⟩
      · rw [blockPoly, hR, show q + 1 + p = q + (p + 1) by omega]
        ring
      · refine (((dependsOnRows_var q q).mono ?_).pow _).mul (hfree.mono ?_)
        · intro l hl
          simp only [Set.mem_singleton_iff] at hl
          simp only [Set.mem_ofPred_eq]
          omega
        · intro l hl
          simp only [Set.mem_ofPred_eq] at hl ⊢
          omega
  | .induced d' :: ds, q, 0, d, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      refine ⟨blockPoly n ds (q + 2), by rw [blockPoly, add_zero], ?_⟩
      refine (dependsOnRows_blockPoly ds (q + 2)).mono ?_
      intro l hl
      simp only [Set.mem_ofPred_eq] at hl ⊢
      omega
  | .induced _ :: _, _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced d' :: ds, q, p + 2, d, h => by
      obtain ⟨R, hR, hfree⟩ := exists_blockPoly_eq_blockFactor_mul ds (q + 2) p d h
      refine ⟨blockFactor n q (d'.weight.natAbs + 1) * R, ?_, ?_⟩
      · rw [blockPoly, hR, show q + 2 + p = q + (p + 2) by omega]
        ring
      · refine ((dependsOnRows_blockFactor q _).mono ?_).mul (hfree.mono ?_)
        · intro l hl
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
          simp only [Set.mem_ofPred_eq]
          omega
        · intro l hl
          simp only [Set.mem_ofPred_eq] at hl ⊢
          omega

/-! ## Rotation of two rows -/

/-- `Y'` is obtained from `Y` by rotating the rows `p, p + 1` by `(u, v)`:
row `p` becomes `u Y_p - v Y_{p+1}`, row `p + 1` becomes `v Y_p + u Y_{p+1}`. -/
def IsRowRotation {p : ℕ} (h : p + 1 < n) (u v : ℂ) (Y Y' : Fin n × Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i ≠ ia h → i ≠ ib h → Y' (i, j) = Y (i, j)) ∧
    (∀ j : Fin n, Y' (ia h, j) = u * Y (ia h, j) - v * Y (ib h, j)) ∧
    ∀ j : Fin n, Y' (ib h, j) = v * Y (ia h, j) + u * Y (ib h, j)

theorem eval_lplus_rotation {p : ℕ} (h : p + 1 < n) {u v : ℂ} {Y Y' : Fin n × Fin n → ℂ}
    (hY : IsRowRotation h u v Y Y') :
    MvPolynomial.eval Y' (lplus n p) = (u - Complex.I * v) * MvPolynomial.eval Y (lplus n p) := by
  rw [eval_lplus h, eval_lplus h, hY.2.1, hY.2.1, hY.2.2, hY.2.2]
  linear_combination (v * Y (ia h, ib h) - v * Y (ib h, ia h)) * Complex.I_sq

theorem eval_lminus_rotation {p : ℕ} (h : p + 1 < n) {u v : ℂ} {Y Y' : Fin n × Fin n → ℂ}
    (hY : IsRowRotation h u v Y Y') :
    MvPolynomial.eval Y' (lminus n p) =
      (u + Complex.I * v) * MvPolynomial.eval Y (lminus n p) := by
  rw [eval_lminus h, eval_lminus h, hY.2.1, hY.2.1, hY.2.2, hY.2.2]
  linear_combination (v * Y (ia h, ib h) + v * Y (ib h, ia h)) * Complex.I_sq

/-- **Rotation formula.** Rotating the rows `p, p + 1` of the argument of `Φ_p · R`, with `R`
free of these rows, gives `((u - iv)^N ℓ₊^N + (-1)^N (u + iv)^N ℓ₋^N) · R`. -/
theorem eval_rotated_blockFactor_mul {p : ℕ} (h : p + 1 < n) (N : ℕ)
    {R : MvPolynomial (Fin n × Fin n) ℂ} (hR : DependsOnRows {l | l ≠ p ∧ l ≠ p + 1} R)
    {u v : ℂ} {Y Y' : Fin n × Fin n → ℂ} (hY : IsRowRotation h u v Y Y') :
    MvPolynomial.eval Y' (blockFactor n p N * R) =
      ((u - Complex.I * v) ^ N * MvPolynomial.eval Y (lplus n p) ^ N +
        (-1 : ℂ) ^ N * (u + Complex.I * v) ^ N * MvPolynomial.eval Y (lminus n p) ^ N) *
        MvPolynomial.eval Y R := by
  have hR' : MvPolynomial.eval Y' R = MvPolynomial.eval Y R := by
    refine hR Y' Y fun i j hi => hY.1 i j (fun e => hi.1 ?_) (fun e => hi.2 ?_)
    · rw [e]; rfl
    · rw [e]; rfl
  rw [map_mul, hR', eval_blockFactor, eval_lplus_rotation h hY, eval_lminus_rotation h hY,
    mul_pow, mul_pow]
  ring

/-! ## Exponents of an induction block -/

theorem realPositionExponent_of_blockAt : ∀ {ds : List RealBlock} {p : ℕ}
    {d : ComplexCharacterData}, realInducedBlockAt ds p = some d →
    realPositionExponent ds p - realPositionExponent ds (p + 1) = (d.weight.natAbs : ℂ)
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => by
      simp only [realPositionExponent]
      exact realPositionExponent_of_blockAt (ds := ds) (p := p) h
  | .induced d' :: _, 0, d, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      simp only [realPositionExponent]
      ring
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => by
      simp only [realPositionExponent]
      exact realPositionExponent_of_blockAt (ds := ds) (p := p) h

end RealStandardNontrivial

end Langlands.Archimedean
