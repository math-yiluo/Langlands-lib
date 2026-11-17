import Langlands.Representation.Archimedean.ComplexSphericalJacquet
import Langlands.Representation.Archimedean.ComplexBlockFunctionalSized
import Langlands.Representation.Archimedean.ComplexBlockChartBound
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof

/-!
# Cyclicity of the spherical vector with tied blocks

For phase-power characters trivial on phases whose exponents are tied within consecutive blocks
and strictly decrease between blocks (`ComplexBlockFunctional.BlockOrdered ks e`), the block
Jacquet functional `ComplexBlockFunctional.jac ks e 0` does not vanish on the spherical vector
(`ComplexSphericalFace.jac_ne_zero`). Each block step is a Gindikin–Karpelevich-type integral
`∫_{M_{(k+1)×a}(ℂ)} T(n̄(X)) dX`, computed one row at a time:

* along `n̄(X)` the spherical vector is a product of complex powers of the Gram determinants
  `D_l(X) = det(1 + X_{<l}ᴴ X_{<l})` and `E_j(X) = det(1 + X^{(j)ᴴ} X^{(j)})`
  (`ComplexSphericalFace.apply_blockLower`);
* appending a row `x` multiplies `D_l` by `1 + |(x M)_{<l}|²` for a triangular change of variables
  `M` read off from the Iwasawa decomposition of `n̄(X)` (`ComplexSphericalFace.exists_triangular`);
* so each row contributes a nonzero iterated rank-one integral
  (`ComplexSphericalFace.integral_psi_ne_zero`).

With `complexBlockFunctionalSized`, the spherical vector is cyclic
(`complexSphericalBlockCyclic`, and `ComplexSphericalFaceCyclicStatement` for nonincreasing real
parts, proved as `complexSphericalFaceCyclic` via the maximal runs of equal real part).
-/

noncomputable section

open MeasureTheory Set

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator ComplexConjugate TensorProduct ComplexOrder

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexSphericalFace

/-! ## Masked Gram determinants -/

section Gram

variable {m a : ℕ}

/-- `X` with the columns `≥ l` replaced by `0`. -/
def maskC (l : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : Matrix (Fin m) (Fin a) ℂ :=
  Matrix.of fun i c => if (c : ℕ) < l then X i c else 0

/-- `X` with the rows `< j` replaced by `0`. -/
def maskR (j : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : Matrix (Fin m) (Fin a) ℂ :=
  Matrix.of fun i c => if j ≤ (i : ℕ) then X i c else 0

/-- `det(1 + Yᴴ Y)`. -/
def gramC (Y : Matrix (Fin m) (Fin a) ℂ) : ℂ := (1 + Yᴴ * Y).det

theorem gramC_pos (Y : Matrix (Fin m) (Fin a) ℂ) : 0 < gramC Y :=
  show (0 : ℂ) < (1 + Yᴴ * Y).det from (Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y)).det_pos

theorem gramC_eq_re (Y : Matrix (Fin m) (Fin a) ℂ) : gramC Y = ((gramC Y).re : ℂ) :=
  Complex.ext (by simp) (by simp [(Complex.pos_iff.mp (gramC_pos Y)).2])

theorem gramC_re_pos (Y : Matrix (Fin m) (Fin a) ℂ) : 0 < (gramC Y).re :=
  (Complex.pos_iff.mp (gramC_pos Y)).1

/-- `D_l(X) = det(1 + X_{<l}ᴴ X_{<l})` (columns `< l`). -/
def cG (l : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : ℝ := (gramC (maskC l X)).re

/-- `E_j(X) = det(1 + X^{(j)ᴴ} X^{(j)})` (rows `≥ j`). -/
def rG (j : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : ℝ := (gramC (maskR j X)).re

theorem cG_pos (l : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : 0 < cG l X := gramC_re_pos _

theorem rG_pos (j : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) : 0 < rG j X := gramC_re_pos _

theorem maskC_of_le {l : ℕ} (hl : a ≤ l) (X : Matrix (Fin m) (Fin a) ℂ) : maskC l X = X := by
  ext i c
  simp only [maskC, Matrix.of_apply]
  rw [ite_eq_left (by omega)]

theorem maskR_zero (X : Matrix (Fin m) (Fin a) ℂ) : maskR 0 X = X := by
  ext i c
  simp [maskR]

theorem cG_eq_rG_zero (X : Matrix (Fin m) (Fin a) ℂ) : cG a X = rG 0 X := by
  rw [cG, rG, maskC_of_le le_rfl, maskR_zero]

theorem gramC_zero_rows (Y : Matrix (Fin 0) (Fin a) ℂ) : gramC Y = 1 := by
  have : Yᴴ * Y = 0 := by
    ext p q
    simp [Matrix.mul_apply]
  rw [gramC, this, add_zero, Matrix.det_one]

theorem cG_zero_rows (l : ℕ) (X : Matrix (Fin 0) (Fin a) ℂ) : cG l X = 1 := by
  rw [cG, gramC_zero_rows, Complex.one_re]

theorem rG_zero_rows (j : ℕ) (X : Matrix (Fin 0) (Fin a) ℂ) : rG j X = 1 := by
  rw [rG, gramC_zero_rows, Complex.one_re]

/-- The Gram matrix of the masked columns is a sum over the rows. -/
theorem maskC_gram_apply (l : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) (p q : Fin a) :
    ((maskC l X)ᴴ * maskC l X) p q =
      ∑ i : Fin m, if (p : ℕ) < l ∧ (q : ℕ) < l then star (X i p) * X i q else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, maskC, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : (p : ℕ) < l <;> by_cases hq : (q : ℕ) < l <;> simp [hp, hq]

theorem cG_cons_eq_snoc (l : ℕ) (x : Fin a → ℂ) (X : Fin m → Fin a → ℂ) :
    cG l (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) =
      cG l (Matrix.of (Fin.snoc X x : Fin (m + 1) → Fin a → ℂ)) := by
  have h : (maskC l (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)))ᴴ *
      maskC l (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) =
      (maskC l (Matrix.of (Fin.snoc X x : Fin (m + 1) → Fin a → ℂ)))ᴴ *
      maskC l (Matrix.of (Fin.snoc X x : Fin (m + 1) → Fin a → ℂ)) := by
    ext p q
    rw [maskC_gram_apply, maskC_gram_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.snoc_castSucc]
    ring
  rw [cG, cG, gramC, gramC, h]

theorem maskR_gram_apply (j : ℕ) (X : Matrix (Fin m) (Fin a) ℂ) (p q : Fin a) :
    ((maskR j X)ᴴ * maskR j X) p q =
      ∑ i : Fin m, if j ≤ (i : ℕ) then star (X i p) * X i q else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, maskR, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : j ≤ (i : ℕ) <;> simp [hi]

theorem rG_cons_succ (j : ℕ) (x : Fin a → ℂ) (X : Fin m → Fin a → ℂ) :
    rG (j + 1) (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) = rG j (Matrix.of X) := by
  have h : (maskR (j + 1) (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)))ᴴ *
      maskR (j + 1) (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) =
      (maskR j (Matrix.of X))ᴴ * maskR j (Matrix.of X) := by
    ext p q
    rw [maskR_gram_apply, maskR_gram_apply, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ,
      Nat.add_le_add_iff_right]
    rw [ite_eq_right (by omega), zero_add]
  rw [rG, rG, gramC, gramC, h]

/-! ### Relation with the Gram determinants of `n̄(X)` -/

open ComplexBlockParabolic ComplexBlockChart

theorem sum_fromIdx {j : ℕ} (hj : j ≤ m) (g : Fin m → ℂ) :
    ∑ i : Fin (m - j), g (fromIdx hj i) = ∑ i : Fin m, if j ≤ (i : ℕ) then g i else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => fromIdx hj i) (fun i _ => ?_) (fun i _ i' _ h => ?_)
    (fun i hi => ?_) (fun i _ => rfl)
  · simp [fromIdx]
  · have := congrArg Fin.val h
    simp only [fromIdx] at this
    exact Fin.ext (by omega)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨⟨(i : ℕ) - j, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [fromIdx]; omega)⟩

theorem gram_blockLower_eq_cG (X : Matrix (Fin m) (Fin a) ℂ) {l : ℕ} (hl : l ≤ a) :
    ComplexGramFormula.gram l (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (cG l X : ℂ) := by
  have h : colsBelow X hl * (colsBelow X hl)ᴴ = maskC l X * (maskC l X)ᴴ := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colsBelow, Matrix.submatrix_apply,
      id, maskC, Matrix.of_apply]
    rw [sum_castLE hl (fun c => X i c * star (X k c))]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : (c : ℕ) < l <;> simp [hc]
  rw [gram_blockLower_le X hl, h, Matrix.det_one_add_mul_comm, cG, ← gramC_eq_re, gramC]

theorem gram_blockLower_eq_rG (X : Matrix (Fin m) (Fin a) ℂ) {j : ℕ} (hj : j ≤ m) :
    ComplexGramFormula.gram (a + j) (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (rG j X : ℂ) := by
  rw [gram_blockLower_ge X hj, rG, ← gramC_eq_re, gramC, Matrix.det_one_add_mul_comm]
  congr 2
  ext p q
  rw [maskR_gram_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rowsGe, Matrix.submatrix_apply, id]
  exact sum_fromIdx hj (fun i => star (X i p) * X i q)

end Gram

/-! ## The triangular change of variables -/

section Iwasawa

open ComplexBlockParabolic ComplexBlockChart ComplexMaximalParabolicIntegration ComplexPartialJacquet
  ComplexParabolicChartBound Langlands.GeneralLinear

variable {N : ℕ}

theorem mul_apply_self_of_upper {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.IsUpperTriangular)
    (hQ : Q.IsUpperTriangular) (j : Fin N) : (P * Q) j j = P j j * Q j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro i _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · simp

theorem diagonalTail_mul_of_upper {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.IsUpperTriangular)
    (hQ : Q.IsUpperTriangular) (l : ℕ) :
    GramFormula.diagonalTail l (P * Q) =
      GramFormula.diagonalTail l P * GramFormula.diagonalTail l Q := by
  simp only [GramFormula.diagonalTail, mul_apply_self_of_upper hP hQ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem isUpperTriangular_iota {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsUpperTriangular) :
    (iota A).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  refine Fin.lastCases (motive := fun i => j < i → iota A i j = 0) ?_ (fun i' => ?_) i hij
  · refine Fin.lastCases (motive := fun j => j < Fin.last N → iota A (Fin.last N) j = 0) ?_
      (fun j' _ => ?_) j
    · intro h
      exact absurd h (lt_irrefl _)
    · simp
  · refine Fin.lastCases (motive := fun j => j < i'.castSucc → iota A i'.castSucc j = 0) ?_
      (fun j' h => ?_) j
    · intro h
      exact absurd h (not_lt.mpr (Fin.le_last _))
    · rw [iota_castSucc_castSucc]
      exact hA (Fin.castSucc_lt_castSucc_iff.mp h)

theorem diagonalTail_iota (A : Matrix (Fin N) (Fin N) ℂ) (l : ℕ) :
    GramFormula.diagonalTail l (iota A) = GramFormula.diagonalTail l A := by
  simp only [GramFormula.diagonalTail]
  rw [Fin.prod_univ_castSucc]
  simp only [iota_castSucc_castSucc, Fin.val_castSucc, iota_last_last, ite_self, mul_one]

/-- **Gram determinants of `ι(b) J(w, 1) ι(κ)`.** For `b` upper triangular, `κ ∈ U(N)` and
`l ≤ N`, `G_l(ι(b) J(w,1) ι(κ)) = |∏_{j ≥ l} b_{jj}|² · r_l(w)`. -/
theorem gram_iota_mul_chartGL (b : Langlands.GeneralLinear N ℂ)
    (hb : (b : Matrix (Fin N) (Fin N) ℂ).IsUpperTriangular) (w : Fin N → ℂ)
    {κ : Langlands.GeneralLinear N ℂ} (hκ : κ ∈ unitaryCompact ℂ N) {l : ℕ} (hl : l ≤ N) :
    ComplexGramFormula.gram l
        ((iotaGL b * chartGL w * iotaGL κ : Langlands.GeneralLinear (N + 1) ℂ) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        (((iotaGL b * chartGL w * iotaGL κ : Langlands.GeneralLinear (N + 1) ℂ) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).map (starRingEnd ℂ)) =
      ((‖GramFormula.diagonalTail l (b : Matrix (Fin N) (Fin N) ℂ)‖ ^ 2 * partialSq w l : ℝ) :
        ℂ) := by
  obtain ⟨d, u, k, hk, hc⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary (chartGL w)
  have hmat : ((iotaGL b * chartGL w * iotaGL κ : Langlands.GeneralLinear (N + 1) ℂ) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
      (iota (b : Matrix (Fin N) (Fin N) ℂ) * (Matrix.diagonal (fun i => (d i : ℂ)) *
        ((u : Langlands.GeneralLinear (N + 1) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))) *
      ((k : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * iota (κ : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [hc]
    simp only [Units.val_mul, iotaGL_val, Iwasawa.diagonalUnits_val, Matrix.mul_assoc]
  have hB := (isUpperTriangular_iota hb).mul (ComplexGramFormula.isUpperTriangular_diagonal_mul d u)
  have hK : ((k : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * iota (κ : Matrix (Fin N) (Fin N) ℂ)) *
      (((k : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *
        iota (κ : Matrix (Fin N) (Fin N) ℂ)).map (starRingEnd ℂ))ᵀ = 1 := by
    have := ComplexGramFormula.mul_conj_transpose_eq_one_of_mem
      (mul_mem hk (iotaGL_mem_unitaryCompact hκ))
    simpa only [Units.val_mul, iotaGL_val] using this
  have htail := prod_tail_sq_eq w 1 (unitaryCompact ℂ (N + 1)).one_mem d u k hk
    (by rw [mul_one]; exact hc) hl
  have hdu : GramFormula.diagonalTail l (Matrix.diagonal (fun i => (d i : ℂ)) *
      ((u : Langlands.GeneralLinear (N + 1) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) =
      ∏ j : Fin (N + 1), if l ≤ (j : ℕ) then (d j : ℂ) else 1 := by
    simp only [GramFormula.diagonalTail, ComplexGramFormula.diagonal_mul_apply_self]
  rw [hmat, ComplexGramFormula.gram_mul_conj hB hK l,
    diagonalTail_mul_of_upper (isUpperTriangular_iota hb)
      (ComplexGramFormula.isUpperTriangular_diagonal_mul d u), diagonalTail_iota, norm_mul,
    mul_pow, hdu, htail]

end Iwasawa

/-! ### `n̄(X', x)` as `J(v, 1) ι(n̄(X'))` -/

section Snoc

open ComplexBlockParabolic

variable {m a : ℕ}

@[simp] theorem blockLower_castAdd_castAdd (X : Matrix (Fin m) (Fin a) ℂ) (c c' : Fin a) :
    blockLower X (Fin.castAdd m c) (Fin.castAdd m c') = (1 : Matrix (Fin a) (Fin a) ℂ) c c' := by
  simp [blockLower, Matrix.reindex_apply]

@[simp] theorem blockLower_castAdd_natAdd (X : Matrix (Fin m) (Fin a) ℂ) (c : Fin a)
    (q : Fin m) : blockLower X (Fin.castAdd m c) (Fin.natAdd a q) = 0 := by
  simp [blockLower, Matrix.reindex_apply]

@[simp] theorem blockLower_natAdd_castAdd (X : Matrix (Fin m) (Fin a) ℂ) (q : Fin m)
    (c : Fin a) : blockLower X (Fin.natAdd a q) (Fin.castAdd m c) = X q c := by
  simp [blockLower, Matrix.reindex_apply]

@[simp] theorem blockLower_natAdd_natAdd (X : Matrix (Fin m) (Fin a) ℂ) (q q' : Fin m) :
    blockLower X (Fin.natAdd a q) (Fin.natAdd a q') = (1 : Matrix (Fin m) (Fin m) ℂ) q q' := by
  simp [blockLower, Matrix.reindex_apply]

theorem castSucc_castAdd (c : Fin a) :
    (Fin.castSucc (Fin.castAdd m c) : Fin (a + m + 1)) = Fin.castAdd (m + 1) c := Fin.ext rfl

theorem castSucc_natAdd (q : Fin m) :
    (Fin.castSucc (Fin.natAdd a q) : Fin (a + m + 1)) = Fin.natAdd a (Fin.castSucc q) :=
  Fin.ext rfl

theorem last_eq_natAdd : (Fin.last (a + m) : Fin (a + m + 1)) = Fin.natAdd a (Fin.last m) :=
  Fin.ext rfl

open ComplexMaximalParabolicIntegration in
theorem Jmat_mul_iota_apply_castSucc (r : Fin (a + m + 1) → ℂ)
    (B : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) (i : Fin (a + m)) (j : Fin (a + m + 1)) :
    (Jmat r * iota B) (Fin.castSucc i) j = iota B (Fin.castSucc i) j := by
  rw [Matrix.mul_apply]
  simp only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc]
  rw [Finset.sum_eq_single (Fin.castSucc i)]
  · simp
  · intro p _ hp
    rw [Matrix.one_apply_ne (Ne.symm hp), zero_mul]
  · simp

open ComplexMaximalParabolicIntegration in
theorem Jmat_mul_iota_apply_last (r : Fin (a + m + 1) → ℂ)
    (B : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) (j : Fin (a + m + 1)) :
    (Jmat r * iota B) (Fin.last (a + m)) j =
      ∑ p : Fin (a + m), r (Fin.castSucc p) * iota B (Fin.castSucc p) j +
        r (Fin.last (a + m)) * iota B (Fin.last (a + m)) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Jmat, Matrix.of_apply, Fin.lastCases_last]

open ComplexMaximalParabolicIntegration ComplexBlockParabolic Langlands.GeneralLinear in
/-- `n̄(X'; x) = J(v, 1) ι(n̄(X'))` with `v = (x, 0)`, where `n̄(X'; x)` has the rows of `X'`
followed by `x`. -/
theorem blockLower_snoc (X : Fin m → Fin a → ℂ) (x : Fin a → ℂ) :
    (blockLowerGL (a := a) (k := m + 1) (Matrix.of (Fin.snoc X x)) :
      Langlands.GeneralLinear (a + m + 1) ℂ) =
      chartGL (Fin.append x (0 : Fin m → ℂ)) *
        iotaGL (blockLowerGL (a := a) (k := m) (Matrix.of X)) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, iotaGL_val, ComplexBlockChart.blockLowerGL_val]
  refine Matrix.ext fun (i : Fin (a + m + 1)) (j : Fin (a + m + 1)) => ?_
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [Jmat_mul_iota_apply_last]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [iota_castSucc_last, mul_zero, Finset.sum_const_zero, zero_add, Fin.snoc_last,
        iota_last_last, mul_one]
      rw [last_eq_natAdd, show (Fin.natAdd a (Fin.last m) : Fin (a + (m + 1))) =
        Fin.natAdd a (Fin.last m) from rfl, blockLower_natAdd_natAdd, Matrix.one_apply_eq]
    · simp only [iota_castSucc_castSucc, iota_last_castSucc, mul_zero, add_zero, Fin.snoc_castSucc]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      refine Fin.addCases (fun c => ?_) (fun q => ?_) j'
      · rw [castSucc_castAdd, last_eq_natAdd]
        simp only [blockLower_castAdd_castAdd, blockLower_natAdd_castAdd, Matrix.of_apply,
          Fin.snoc_last]
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hc
          rw [Matrix.one_apply_ne hc, mul_zero]
        · simp
      · rw [castSucc_natAdd, last_eq_natAdd]
        simp only [blockLower_castAdd_natAdd, blockLower_natAdd_natAdd, mul_zero,
          Finset.sum_const_zero]
        rw [Matrix.one_apply_ne (Fin.castSucc_ne_last q).symm]
  · rw [Jmat_mul_iota_apply_castSucc]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [iota_castSucc_last]
      refine Fin.addCases (fun c => ?_) (fun q => ?_) i'
      · rw [castSucc_castAdd, last_eq_natAdd, blockLower_castAdd_natAdd]
      · rw [castSucc_natAdd, last_eq_natAdd, blockLower_natAdd_natAdd,
          Matrix.one_apply_ne (Fin.castSucc_ne_last q)]
    · rw [iota_castSucc_castSucc]
      refine Fin.addCases (fun c => ?_) (fun q => ?_) i' <;>
        refine Fin.addCases (fun c' => ?_) (fun q' => ?_) j'
      · rw [castSucc_castAdd, castSucc_castAdd, blockLower_castAdd_castAdd,
          blockLower_castAdd_castAdd]
      · rw [castSucc_castAdd, castSucc_natAdd, blockLower_castAdd_natAdd,
          blockLower_castAdd_natAdd]
      · rw [castSucc_natAdd, castSucc_castAdd, blockLower_natAdd_castAdd,
          blockLower_natAdd_castAdd, Matrix.of_apply, Fin.snoc_castSucc, Matrix.of_apply]
      · rw [castSucc_natAdd, castSucc_natAdd, blockLower_natAdd_natAdd,
          blockLower_natAdd_natAdd, Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.castSucc_inj]

open ComplexParabolicChartBound in
theorem partialSq_append_vecMul (x : Fin a → ℂ) (B : Matrix (Fin (a + m)) (Fin (a + m)) ℂ)
    {l : ℕ} (hl : l ≤ a) :
    partialSq (Fin.append x (0 : Fin m → ℂ) ᵥ* B) l =
      partialSq (x ᵥ* Matrix.of fun i j => B (Fin.castAdd m i) (Fin.castAdd m j)) l := by
  have hv : ∀ j, (Fin.append x (0 : Fin m → ℂ) ᵥ* B) j = ∑ i : Fin a, x i * B (Fin.castAdd m i) j :=
    fun j => by
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [partialSq, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, hv]
  have h0 : ∀ q : Fin m, (if a + (q : ℕ) < l then
      ‖∑ i : Fin a, x i * B (Fin.castAdd m i) (Fin.natAdd a q)‖ ^ 2 else 0) = 0 :=
    fun q => ite_eq_right (by omega)
  simp only [h0, Finset.sum_const_zero, add_zero, Matrix.vecMul, dotProduct, Matrix.of_apply]

open ComplexMaximalParabolicIntegration ComplexPartialJacquet ComplexParabolicChartBound
  Langlands.GeneralLinear in
/-- **The triangular change of variables.** For `X ∈ M_{m×a}(ℂ)` there is an invertible `M` with
`|det M|⁻² = D_a(X)` and `D_l(X; x) = D_l(X) · r_l(x M)` for all `x ∈ ℂ^a` and `l ≤ a`, where
`(X; x)` is `X` with the row `x` appended. `M` is the top left `a × a` block of the triangular
factor of the Iwasawa decomposition of `n̄(X)`. -/
theorem exists_triangular (X : Fin m → Fin a → ℂ) :
    ∃ M : Matrix (Fin a) (Fin a) ℂ, M.det ≠ 0 ∧ (‖M.det‖ ^ 2)⁻¹ = cG a (Matrix.of X) ∧
      ∀ (x : Fin a → ℂ) (l : ℕ), l ≤ a →
        cG l (Matrix.of (Fin.snoc X x)) = cG l (Matrix.of X) * partialSq (x ᵥ* M) l := by
  obtain ⟨α, u, κ, hκ, hg⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary
    (blockLowerGL (a := a) (k := m) (Matrix.of X))
  set b : Langlands.GeneralLinear (a + m) ℂ :=
    (Iwasawa.diagonalUnits α : Langlands.GeneralLinear (a + m) ℂ) *
      (u : Langlands.GeneralLinear (a + m) ℂ) with hbdef
  have hbval : (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) =
      Matrix.diagonal (fun i => (α i : ℂ)) *
        ((u : Langlands.GeneralLinear (a + m) ℂ) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) := by
    rw [hbdef, Units.val_mul, Iwasawa.diagonalUnits_val]
  have hb : (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ).IsUpperTriangular := by
    rw [hbval]
    exact ComplexGramFormula.isUpperTriangular_diagonal_mul α u
  have hbdiag : ∀ j, (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) j j = α j := fun j => by
    rw [hbval, ComplexGramFormula.diagonal_mul_apply_self]
  have hgb : blockLowerGL (a := a) (k := m) (Matrix.of X) = b * κ := hg
  have hgram : ∀ l, ComplexGramFormula.gram l (blockLower (a := a) (k := m) (Matrix.of X))
      ((blockLower (a := a) (k := m) (Matrix.of X)).map (starRingEnd ℂ)) =
      ((‖GramFormula.diagonalTail l (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ)‖ ^ 2 : ℝ) :
        ℂ) := by
    intro l
    have h := ComplexGramFormula.gram_mul_conj hb
      (ComplexGramFormula.mul_conj_transpose_eq_one_of_mem hκ) l
    rw [← Units.val_mul, ← hgb, ComplexBlockChart.blockLowerGL_val] at h
    exact h
  have hcG : ∀ l, l ≤ a → cG l (Matrix.of X) =
      ‖GramFormula.diagonalTail l (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ)‖ ^ 2 := by
    intro l hl
    have h := (gram_blockLower_eq_cG (Matrix.of X) hl).symm.trans (hgram l)
    exact_mod_cast h
  set M : Matrix (Fin a) (Fin a) ℂ :=
    Matrix.of fun i j => (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) (Fin.castAdd m i)
      (Fin.castAdd m j) with hMdef
  have hMup : M.IsUpperTriangular := fun i j h => by
    simp only [hMdef, Matrix.of_apply]
    exact hb (show Fin.castAdd m j < Fin.castAdd m i from h)
  have hMdet : M.det = ∏ i : Fin a, (α (Fin.castAdd m i) : ℂ) := by
    rw [Matrix.det_of_isUpperTriangular hMup]
    simp only [hMdef, Matrix.of_apply, hbdiag]
  have htail0 : GramFormula.diagonalTail 0 (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) =
      M.det * ∏ q : Fin m, (α (Fin.natAdd a q) : ℂ) := by
    simp only [GramFormula.diagonalTail, Nat.zero_le, ite_true, hbdiag, hMdet, Fin.prod_univ_add]
  have htaila : GramFormula.diagonalTail a (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ) =
      ∏ q : Fin m, (α (Fin.natAdd a q) : ℂ) := by
    simp only [GramFormula.diagonalTail, hbdiag, Fin.prod_univ_add, Fin.val_castAdd,
      Fin.val_natAdd]
    rw [Finset.prod_eq_one (fun i _ => ite_eq_right (by have := i.isLt; omega))]
    simp
  have hcG0 : cG 0 (Matrix.of X) = 1 := by
    have : maskC 0 (Matrix.of X) = 0 := by
      ext i c
      simp [maskC]
    rw [cG, this, gramC, Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero, Matrix.det_one,
      Complex.one_re]
  have hdet : (‖M.det‖ ^ 2)⁻¹ = cG a (Matrix.of X) := by
    have h0 := hcG 0 (Nat.zero_le a)
    rw [hcG0, htail0, norm_mul, mul_pow] at h0
    rw [hcG a le_rfl, htaila]
    have hpos : 0 < ‖M.det‖ ^ 2 := by
      rcases eq_or_lt_of_le (sq_nonneg ‖M.det‖) with h | h
      · rw [← h, zero_mul] at h0
        exact absurd h0 one_ne_zero
      · exact h
    rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hpos.ne', mul_comm]
    exact h0.symm
  have hMne : M.det ≠ 0 := by
    rw [hMdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (α _).ne_zero
  refine ⟨M, hMne, hdet, fun x l hl => ?_⟩
  have key : (blockLowerGL (a := a) (k := m + 1) (Matrix.of (Fin.snoc X x)) :
      Langlands.GeneralLinear (a + m + 1) ℂ) =
      iotaGL b * chartGL (Fin.append x (0 : Fin m → ℂ) ᵥ*
        (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ)) * iotaGL κ := by
    rw [blockLower_snoc, hgb, map_mul, ← mul_assoc, chartGL_mul_iotaGL]
  have h1 := gram_iota_mul_chartGL b hb (Fin.append x (0 : Fin m → ℂ) ᵥ*
    (b : Matrix (Fin (a + m)) (Fin (a + m)) ℂ)) hκ (l := l) (by omega)
  rw [← key, ComplexBlockChart.blockLowerGL_val] at h1
  have h2 := (gram_blockLower_eq_cG (Matrix.of (Fin.snoc X x)) hl).symm.trans h1
  rw [hcG l hl, ← partialSq_append_vecMul x _ hl]
  exact_mod_cast h2

end Snoc

/-! ## The Gindikin–Karpelevich integral of a tied block -/

section Integral

open ComplexSphericalJacquet ComplexPartialSqIntegral ComplexParabolicChartBound

variable {a : ℕ}

/-- The integrand `Ψ_m(s, w, t)(X) = D_a(X)^w ∏_{l<a} D_{l+1}(X)^{s_l} ∏_{1 ≤ j < m} E_j(X)^{t_j}`
on `M_{m×a}(ℂ)`. -/
def psi (m : ℕ) (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) (X : Fin m → Fin a → ℂ) : ℂ :=
  ((cG a (Matrix.of X) : ℝ) : ℂ) ^ w *
    (∏ l : Fin a, ((cG ((l : ℕ) + 1) (Matrix.of X) : ℝ) : ℂ) ^ s l) *
    ∏ j ∈ Finset.Ico 1 m, ((rG j (Matrix.of X) : ℝ) : ℂ) ^ t j

theorem psi_zero (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) (X : Fin 0 → Fin a → ℂ) :
    psi 0 s w t X = 1 := by
  simp [psi, cG_zero_rows]

theorem ofReal_mul_cpow {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (z : ℂ) :
    (((p * q : ℝ)) : ℂ) ^ z = (p : ℂ) ^ z * (q : ℂ) ^ z := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp hq]

/-- **Peeling the first row.** -/
theorem psi_cons {m : ℕ} (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) (X : Fin m → Fin a → ℂ)
    {M : Matrix (Fin a) (Fin a) ℂ}
    (hM : ∀ (x : Fin a → ℂ) (l : ℕ), l ≤ a →
      cG l (Matrix.of (Fin.snoc X x)) = cG l (Matrix.of X) * partialSq (x ᵥ* M) l)
    (x : Fin a → ℂ) :
    psi (m + 1) s w t (Fin.cons x X) =
      (((cG a (Matrix.of X) : ℝ) : ℂ) ^ w *
        (∏ l : Fin a, ((cG ((l : ℕ) + 1) (Matrix.of X) : ℝ) : ℂ) ^ s l) *
        ∏ j ∈ Finset.range m, ((rG j (Matrix.of X) : ℝ) : ℂ) ^ t (j + 1)) *
      chartFun a s w (x ᵥ* M) := by
  have hc : ∀ l, l ≤ a → cG l (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) =
      cG l (Matrix.of X) * partialSq (x ᵥ* M) l := fun l hl => by
    rw [cG_cons_eq_snoc, hM x l hl]
  have hr : ∏ j ∈ Finset.Ico 1 (m + 1),
      ((rG j (Matrix.of (Fin.cons x X : Fin (m + 1) → Fin a → ℂ)) : ℝ) : ℂ) ^ t j =
      ∏ j ∈ Finset.range m, ((rG j (Matrix.of X) : ℝ) : ℂ) ^ t (j + 1) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [add_comm 1 j, rG_cons_succ]
  have h0 : ∀ l, 0 ≤ cG l (Matrix.of X) := fun l => (cG_pos l _).le
  have h1 : ∀ (y : Fin a → ℂ) l, 0 ≤ partialSq y l := fun y l => (partialSq_pos y l).le
  rw [psi, hr, hc a le_rfl, ofReal_mul_cpow (h0 a) (h1 _ a)]
  rw [Finset.prod_congr rfl fun (l : Fin a) _ => by
    rw [hc ((l : ℕ) + 1) l.isLt, ofReal_mul_cpow (h0 _) (h1 _ _)], Finset.prod_mul_distrib,
    chartFun]
  ring

theorem psi_merge {m : ℕ} (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) (X : Fin m → Fin a → ℂ) :
    (((cG a (Matrix.of X) : ℝ) : ℂ) ^ w *
        (∏ l : Fin a, ((cG ((l : ℕ) + 1) (Matrix.of X) : ℝ) : ℂ) ^ s l) *
        ∏ j ∈ Finset.range m, ((rG j (Matrix.of X) : ℝ) : ℂ) ^ t (j + 1)) *
      ((cG a (Matrix.of X) : ℝ) : ℂ) = psi m s (w + 1 + t 1) (fun j => t (j + 1)) X := by
  cases m with
  | zero => simp [psi, cG_zero_rows]
  | succ m =>
    have hG : ((cG a (Matrix.of X) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (cG_pos a _).ne'
    rw [Finset.prod_range_eq_mul_Ico _ (Nat.succ_pos m), ← cG_eq_rG_zero, psi,
      Complex.cpow_add _ _ hG, Complex.cpow_add _ _ hG, Complex.cpow_one]
    ring

open ComplexPartialJacquet in
/-- **One row of the Gindikin–Karpelevich integral.** -/
theorem integral_psi_succ {m : ℕ} (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ)
    (hint : Integrable (psi (m + 1) s w t)) :
    ∫ X, psi (m + 1) s w t X =
      (∫ y, chartFun a s w y) * ∫ X, psi m s (w + 1 + t 1) (fun j => t (j + 1)) X := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin a → ℂ) 0
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Fin a → ℂ) 0
  set G : (Fin a → ℂ) × (Fin m → Fin a → ℂ) → ℂ := fun p => psi (m + 1) s w t (Fin.cons p.1 p.2)
    with hGdef
  have key : psi (m + 1) s w t ∘ e.symm = G := by
    funext p
    obtain ⟨x, X⟩ := p
    simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hGdef]
    rw [show (Fin.insertNthEquiv (fun _ : Fin (m + 1) => Fin a → ℂ) 0) (x, X) =
      (Fin.cons x X : Fin (m + 1) → Fin a → ℂ) from Fin.insertNth_zero' _ _]
  have hintG : Integrable G (volume.prod volume) := by
    rw [← key, ← Measure.volume_eq_prod]
    exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hint
  have h1 : ∫ X, psi (m + 1) s w t X = ∫ p, G p ∂(volume.prod volume) := by
    rw [← key, ← Measure.volume_eq_prod]
    exact (hmp.symm.integral_comp' (psi (m + 1) s w t)).symm
  rw [h1, integral_prod_symm G hintG, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun X => ?_)
  obtain ⟨M, hMdet, hdet, hM⟩ := exists_triangular X
  simp only [hGdef]
  simp_rw [psi_cons s w t X hM]
  rw [integral_const_mul, integral_vecMul_eq hMdet (chartFun a s w), hdet, ← psi_merge]
  ring

theorem integral_psi_zero_rows (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) :
    ∫ X : Fin 0 → Fin a → ℂ, psi 0 s w t X = 1 := by
  rw [integral_congr_ae (ae_of_all _ (psi_zero s w t)), integral_const, Complex.real_smul,
    mul_one, Measure.real, volume_pi, Measure.pi_univ]
  simp

/-! ### Integrability -/

variable {m : ℕ}

theorem continuous_gramC : Continuous (gramC : Matrix (Fin m) (Fin a) ℂ → ℂ) :=
  (continuous_const.add (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)).matrix_det

theorem continuous_cG (l : ℕ) : Continuous fun X : Fin m → Fin a → ℂ => cG l (Matrix.of X) := by
  refine Complex.continuous_re.comp (continuous_gramC.comp (continuous_matrix fun i c => ?_))
  simp only [maskC, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply c).comp (continuous_apply i)
  · exact continuous_const

theorem continuous_rG (j : ℕ) : Continuous fun X : Fin m → Fin a → ℂ => rG j (Matrix.of X) := by
  refine Complex.continuous_re.comp (continuous_gramC.comp (continuous_matrix fun i c => ?_))
  simp only [maskR, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply c).comp (continuous_apply i)
  · exact continuous_const

theorem measurable_psi (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) : Measurable (psi m s w t) :=
  (((Complex.continuous_ofReal.comp (continuous_cG a)).measurable.pow_const w).mul
    (Finset.measurable_prod _ fun _ _ =>
      (Complex.continuous_ofReal.comp (continuous_cG _)).measurable.pow_const _)).mul
    (Finset.measurable_prod _ fun _ _ =>
      (Complex.continuous_ofReal.comp (continuous_rG _)).measurable.pow_const _)

theorem norm_psi (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ) (X : Fin m → Fin a → ℂ) :
    ‖psi m s w t X‖ = cG a (Matrix.of X) ^ w.re *
      (∏ l : Fin a, cG ((l : ℕ) + 1) (Matrix.of X) ^ (s l).re) *
      ∏ j ∈ Finset.Ico 1 m, rG j (Matrix.of X) ^ (t j).re := by
  rw [psi, norm_mul, norm_mul, norm_prod, norm_prod,
    Complex.norm_cpow_eq_rpow_re_of_pos (cG_pos _ _),
    Finset.prod_congr rfl fun (l : Fin a) _ =>
      Complex.norm_cpow_eq_rpow_re_of_pos (cG_pos ((l : ℕ) + 1) (Matrix.of X)) (s l),
    Finset.prod_congr rfl fun (j : ℕ) _ =>
      Complex.norm_cpow_eq_rpow_re_of_pos (rG_pos j (Matrix.of X)) (t j)]

open ComplexBlockParabolic ComplexBlockChart in
theorem norm_psi_eq_bound {k : ℕ} (s : Fin a → ℂ) {w : ℂ} (hw : w.re = 0) {t : ℕ → ℂ}
    (ht : ∀ j, 1 ≤ j → j < k + 1 → (t j).re = -1) (X : Fin (k + 1) → Fin a → ℂ) :
    ‖psi (k + 1) s w t X‖ = blockChartBound (fun l => (s l).re) (Matrix.of X) := by
  have hcol : ∀ l : Fin a, colGram (Matrix.of X) l = cG ((l : ℕ) + 1) (Matrix.of X) := by
    intro l
    rw [← gramRe_blockLower_col, gramRe]
    rw [gram_blockLower_eq_cG _ l.isLt, Complex.ofReal_re]
  have hrow : ∀ j : Fin k, rowGram (Matrix.of X) j.succ = rG ((j : ℕ) + 1) (Matrix.of X) := by
    intro j
    rw [← gramRe_blockLower_row, gramRe]
    rw [gram_blockLower_eq_rG _ (by omega : (j : ℕ) + 1 ≤ k + 1), Complex.ofReal_re]
  rw [norm_psi, hw, Real.rpow_zero, one_mul, blockChartBound, Fin.prod_univ_succ]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by rw [hcol]
  · rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range]
    simp only [Fin.val_zero, ite_true, one_mul, Fin.val_succ, Nat.add_one_ne_zero, ite_false]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [add_comm 1 (j : ℕ), ht _ (by omega) (by omega), Real.rpow_neg_one, hrow]

open ComplexBlockChart in
theorem integrable_psi {k : ℕ} {s : Fin a → ℂ} (hs : TailCondition (fun l => (s l).re) 0)
    {w : ℂ} (hw : w.re = 0) {t : ℕ → ℂ} (ht : ∀ j, 1 ≤ j → j < k + 1 → (t j).re = -1) :
    Integrable (psi (k + 1) s w t) :=
  (complexBlockChartIntegrable a (k + 1) (fun l => (s l).re)
    (fun j => by simpa using hs j)).mono' (measurable_psi s w t).aestronglyMeasurable
    (ae_of_all _ fun X => (norm_psi_eq_bound s hw ht X).le)

/-- **The Gindikin–Karpelevich integral of a tied block does not vanish.** -/
theorem integral_psi_ne_zero : ∀ (m : ℕ) (s : Fin a → ℂ) (w : ℂ) (t : ℕ → ℂ),
    TailCondition (fun l => (s l).re) 0 → w.re = 0 →
    (∀ j, 1 ≤ j → j < m → (t j).re = -1) → ∫ X, psi m s w t X ≠ 0
  | 0, s, w, t, _, _, _ => by rw [integral_psi_zero_rows]; exact one_ne_zero
  | m + 1, s, w, t, hs, hw, ht => by
    have hs' : TailCondition (fun l => (s l).re) w.re := by rw [hw]; exact hs
    rw [integral_psi_succ s w t (integrable_psi hs hw ht)]
    refine mul_ne_zero (integral_chartFun_ne_zero a s w hs') ?_
    cases m with
    | zero => rw [integral_psi_zero_rows]; exact one_ne_zero
    | succ m =>
      refine integral_psi_ne_zero (m + 1) s _ _ hs ?_ fun j hj1 hj2 => ht _ (by omega) (by omega)
      rw [Complex.add_re, Complex.add_re, hw, Complex.one_re, ht 1 le_rfl (by omega)]
      norm_num

end Integral

/-! ## The spherical vector along `n̄(X)` -/

section Spherical

open ComplexSphericalJacquet ComplexPartialSqIntegral ComplexParabolicChartBound
  ComplexBlockParabolic ComplexBlockChart ComplexPartialJacquet ComplexGramFormula
  Langlands.GeneralLinear

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The principal-series character of the diagonal part of the Iwasawa decomposition of `n̄(X)`,
for characters trivial on phases: `∏_{l < a+k} G_{l+1}(n̄(X))^{e_{l+1} - e_l - 1}`. -/
theorem principalSeriesCharacter_blockLower (hχ : IsPhasePower χ e)
    (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) (X : Fin (k + 1) → Fin a → ℂ)
    (z : Fin (a + k + 1) → ℂˣ) (u : upperUnipotent (a + k + 1) ℂ)
    (κ : Langlands.GeneralLinear (a + k + 1) ℂ) (hκ : κ ∈ unitaryCompact ℂ (a + k + 1))
    (hg : (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) :
      Langlands.GeneralLinear (a + k + 1) ℂ) =
      (Iwasawa.diagonalUnits z : Langlands.GeneralLinear (a + k + 1) ℂ) *
        (u : Langlands.GeneralLinear (a + k + 1) ℂ) * κ) :
    principalSeriesCharacter ℂ (a + k + 1) χ z =
      ∏ l : Fin (a + k), ((gramRe (N := a + k) (blockLower (a := a) (k := k + 1) (Matrix.of X))
        ((l : ℕ) + 1) : ℝ) : ℂ) ^ (e ((l : ℕ) + 1) - e l - 1) := by
  have hz : ∀ l, 0 < ‖(z l : ℂ)‖ := fun l => norm_pos_iff.mpr (z l).ne_zero
  set G : ℕ → ℝ := gramRe (N := a + k) (blockLower (a := a) (k := k + 1) (Matrix.of X)) with hGdef
  have hG : ∀ l, G l = ‖∏ j : Fin (a + k + 1), if l ≤ (j : ℕ) then (z j : ℂ) else 1‖ ^ 2 := by
    intro l
    have h := prod_tail_sq_eq_gram (N := a + k) (blockLowerGL (a := a) (k := k + 1) (Matrix.of X)) 1
      (unitaryCompact ℂ (a + k + 1)).one_mem z u κ hκ (by rw [mul_one]; exact hg) l
    rw [blockLowerGL_val] at h
    rw [hGdef, gramRe, h, Complex.ofReal_re]
  set t : Fin (a + k + 1) → ℂ := fun j => ((2 * Real.log ‖(z j : ℂ)‖ : ℝ) : ℂ) with htdef
  set σ : ℕ → ℂ := fun i => e i + (((a + k + 1 : ℕ) : ℂ) - 1) / 2 - (i : ℂ) with hσdef
  set T : ℕ → ℂ := fun l => ∑ j : Fin (a + k + 1), if l ≤ (j : ℕ) then t j else 0 with hTdef
  have hT : ∀ l : ℕ, T l = (Real.log (G l) : ℂ) := by
    intro l
    rw [hG l, Real.log_pow, norm_prod, Real.log_prod]
    · rw [hTdef]
      simp only [htdef]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · intro j _
      split_ifs
      · exact (hz j).ne'
      · simp
  have hT0 : T 0 = 0 := by
    rw [hT 0, hGdef, gramRe_blockLower_zero, Real.log_one, Complex.ofReal_zero]
  have hsum := sum_mul_eq_sum_sub_complex (t := t) (σ := σ) (T := T) (fun l => rfl) hT0
  have hlhs : principalSeriesCharacter ℂ (a + k + 1) χ z =
      Complex.exp (∑ l : Fin (a + k + 1), σ l * t l) := by
    rw [Complex.exp_sum, principalSeriesCharacter]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hpos : (0 : ℝ) < ‖(z i : ℂ)‖ ^ 2 := pow_pos (hz i) 2
    rw [hχ.eq, h0, one_mul, Complex.finrank_real_complex,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne'), ofReal_cpow_eq_exp hpos,
      Real.log_pow]
    congr 1
    simp only [htdef, hσdef]
    push_cast
    ring
  have hrhs : ∏ l : Fin (a + k), ((G ((l : ℕ) + 1) : ℝ) : ℂ) ^ (e ((l : ℕ) + 1) - e l - 1) =
      Complex.exp (∑ l : Fin (a + k), (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hGpos : 0 < G ((l : ℕ) + 1) := by
      have h := gramRe_pos (N := a + k) (blockLowerGL (a := a) (k := k + 1) (Matrix.of X))
        ((l : ℕ) + 1)
      rw [blockLowerGL_val] at h
      exact h
    rw [ofReal_cpow_eq_exp hGpos, hT]
    congr 1
    simp only [hσdef]
    push_cast
    ring
  rw [hlhs, hsum, ← hrhs]

/-- **The spherical vector along `n̄(X)`.** `T(n̄(X)) = T(1) Ψ_{k+1}(s, 0, t)(X)` with
`s_l = e_{l+1} - e_l - 1` and `t_j = e_{a+j} - e_{a+j-1} - 1`. -/
theorem apply_blockLower (hχ : IsPhasePower χ e) (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1)
    {T : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hT : T ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), T κ = T 1) (X : Fin (k + 1) → Fin a → ℂ) :
    T (blockLowerGL (a := a) (k := k + 1) (Matrix.of X)) =
      T 1 * psi (k + 1) (fun l : Fin a => e ((l : ℕ) + 1) - e l - 1) 0
        (fun j => e (a + j) - e (a + j - 1) - 1) X := by
  obtain ⟨z, u, κ, hκ, hg⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary
    (blockLowerGL (a := a) (k := k + 1) (Matrix.of X))
  rw [hg, hT.2 z u κ, hK κ hκ, mul_comm]
  congr 1
  refine (principalSeriesCharacter_blockLower hχ h0 X z u κ hκ hg).trans ?_
  rw [psi, Complex.cpow_zero, one_mul, Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [Fin.val_castAdd, gramRe, gram_blockLower_eq_cG _ (l.isLt : (l : ℕ) + 1 ≤ a),
      Complex.ofReal_re]
  · rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.val_natAdd, gramRe, show a + (j : ℕ) + 1 = a + ((j : ℕ) + 1) by ring,
      gram_blockLower_eq_rG _ (by omega : (j : ℕ) + 1 ≤ k + 1), Complex.ofReal_re,
      add_comm 1 (j : ℕ), show a + ((j : ℕ) + 1) - 1 = a + (j : ℕ) by omega]

open ComplexBlockJacquet in
theorem blockStep_one (hχ : IsPhasePower χ e) (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1)
    {T : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hT : T ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), T κ = T 1) :
    blockStep T 1 = T 1 * ∫ X, psi (k + 1) (fun l : Fin a => e ((l : ℕ) + 1) - e l - 1) 0
      (fun j => e (a + j) - e (a + j - 1) - 1) X := by
  unfold blockStep
  simp only [mul_one]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun X => apply_blockLower hχ h0 hT hK X)

open ComplexBlockJacquet in
/-- **The block Jacquet integral of the spherical vector does not vanish.** -/
theorem blockStep_one_ne_zero (hχ : IsPhasePower χ e)
    (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) (he : IsBlockDominant e a k)
    {T : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hT : T ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), T κ = T 1) (h1 : T 1 ≠ 0) :
    blockStep T 1 ≠ 0 := by
  rw [blockStep_one hχ h0 hT hK]
  refine mul_ne_zero h1 (integral_psi_ne_zero (k + 1) _ 0 _ (fun j => ?_) Complex.zero_re
    fun j hj1 hj2 => ?_)
  · have := tail_h he j
    simp only [Complex.sub_re, Complex.one_re, zero_add]
    exact this
  · have h1 := he.tie j (by omega)
    have h2 := he.tie (j - 1) (by omega)
    rw [show a + (j - 1) = a + j - 1 by omega] at h2
    simp only [Complex.sub_re, Complex.one_re]
    rw [h1, h2]
    ring

end Spherical

/-! ## The block Jacquet functional of the spherical vector -/

section Jac

open ComplexBlockFunctional ComplexBlockJacquet ComplexBlockLimit ComplexBlockParabolic
  ComplexPartialJacquet ComplexGramFormula ComplexJacquetNonvanishing
  ComplexPrincipalSeriesExtension ComplexSphericalJacquet

theorem blockVector_zero_unitary (a k : ℕ) (e : ℕ → ℂ) (κ : unitaryCompact ℂ (k + 1)) :
    blockVector a k e 0 (κ : Langlands.GeneralLinear (k + 1) ℂ) = 1 := by
  have hku : (κ : Langlands.GeneralLinear (k + 1) ℂ) = Unitary.toUnits
      (⟨((κ : Langlands.GeneralLinear (k + 1) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), κ.2⟩ :
        Matrix.unitaryGroup (Fin (k + 1)) ℂ) := Units.ext rfl
  rw [hku, blockVector, phaseVector, extension_unitary]
  simp [phaseMonomial]

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- Pairing the spherical vector against the spherical vector of the last block gives the block
Jacquet integral `blockStep T 1` on all of `U(a)`. -/
theorem blockPair_spherical {T : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hT : T ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), T κ = T 1) {κ₁ : Langlands.GeneralLinear a ℂ}
    (hκ₁ : κ₁ ∈ unitaryCompact ℂ a) :
    blockPair (blockVector a k e 0) T κ₁ = blockStep T 1 := by
  have h : ∀ κ₂ : unitaryCompact ℂ (k + 1),
      blockVector a k e 0 (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) *
        blockStep T (blockDiagGL κ₁ (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) = blockStep T 1 := by
    intro κ₂
    rw [blockVector_zero_unitary, one_mul]
    simp only [blockStep, mul_one]
    exact integral_congr_ae (ae_of_all _ fun X =>
      apply_mul_unitary hT hK _ (blockDiagGL_mem_unitaryCompact hκ₁ κ₂.2))
  rw [blockPair, integral_congr_ae (ae_of_all _ h), integral_const]
  simp

/-- **The block Jacquet functional of the spherical vector does not vanish.** For phase-power
characters trivial on phases with `BlockOrdered ks e`, a `U(n)`-finite principal-series function
`T` constant on `U(n)` with `T(1) ≠ 0` has `jac ks e 0 T ≠ 0`. -/
theorem jac_ne_zero : ∀ (ks : List ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}, IsPhasePower χ e →
    (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) → BlockOrdered ks e →
    ∀ {T : Langlands.GeneralLinear (dim ks) ℂ → ℂ},
    T ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) →
    (∀ κ ∈ unitaryCompact ℂ (dim ks), T κ = T 1) → T 1 ≠ 0 → jac ks e 0 T ≠ 0
  | [], _, _, _, _, _, _, _, _, h1 => h1
  | k :: ks, χ, e, hχ, h0, ⟨he, hks⟩, T, hT, hK, h1 => by
    have hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ ((0 : ℕ → ℤ) l) :=
      fun l z => by rw [h0, Pi.zero_apply, zpow_zero]
    have hφ : Continuous (blockVector (dim ks) k e 0) :=
      (blockVector_mem hχ hp (dim ks) k).1.1.continuous
    rw [jac_cons]
    refine jac_ne_zero ks (isPhasePower_blockShift hχ) (fun l z => ?_) (hks.shift _)
      (blockPair_mem complexBlockChartIntegrable hχ he hT hφ) (fun κ hκ => ?_) ?_
    · rw [blockShiftChar_phase k hp l z, Pi.zero_apply, zpow_zero]
    · rw [blockPair_spherical hT.1 hK hκ,
        blockPair_spherical hT.1 hK (unitaryCompact ℂ (dim ks)).one_mem]
    · rw [blockPair_spherical hT.1 hK (unitaryCompact ℂ (dim ks)).one_mem]
      exact blockStep_one_ne_zero hχ h0 he hT.1 hK h1

end Jac

/-! ## Maximal runs of equal real parts -/

section Runs

open ComplexBlockFunctional ComplexBlockJacquet

/-- **Decomposition into maximal runs.** If the real parts of `e_0, …, e_{n-1}` do not increase,
the maximal runs of equal real part form a block decomposition `ks` with `BlockOrdered ks e`.
Every block has size at most `n`, and less than `n` unless all real parts are equal. -/
theorem exists_blocks (e : ℕ → ℂ) : ∀ n : ℕ,
    (∀ i j : ℕ, i ≤ j → j < n → (e j).re ≤ (e i).re) →
    ∃ ks : List ℕ, dim ks = n ∧ BlockOrdered ks e ∧ (∀ k ∈ ks, k + 1 ≤ n) ∧
      ((∃ i < n, ∃ j < n, (e i).re ≠ (e j).re) → ∀ k ∈ ks, k + 1 < n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hmono
  cases n with
  | zero => exact ⟨[], rfl, trivial, by simp, by simp⟩
  | succ n =>
    have hex : ∃ i, (e i).re = (e n).re := ⟨n, rfl⟩
    classical
    set a := Nat.find hex with hadef
    have ha : (e a).re = (e n).re := Nat.find_spec hex
    have han : a ≤ n := Nat.find_min' hex rfl
    have hlt : ∀ l, l < a → (e l).re ≠ (e n).re := fun l hl => Nat.find_min hex hl
    have hrun : ∀ i, a ≤ i → i ≤ n → (e i).re = (e n).re := fun i h1 h2 =>
      le_antisymm (by rw [← ha]; exact hmono a i h1 (by omega)) (hmono i n h2 (by omega))
    obtain ⟨ks, hdim, hord, hsize, -⟩ := ih a (by omega) fun i j hij hj => hmono i j hij (by omega)
    refine ⟨(n - a) :: ks, ?_, ⟨⟨fun j hj => ?_, fun l hl => ?_, fun l hl => ?_⟩, hord⟩,
      fun k hk => ?_, fun hne k hk => ?_⟩
    · simp only [dim, hdim]
      omega
    · rw [hdim, hrun (a + j) (by omega) (by omega), ha]
    · exact hmono l (l + 1) (by omega) (by omega)
    · rw [hdim] at hl
      have h1 := hmono l (l + 1) (by omega) (by omega)
      have h2 := hlt l (by omega)
      rw [hl, ha] at h1 ⊢
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · have := hsize k hk
        omega
    · have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · obtain ⟨i, hi, j, hj, hij⟩ := hne
          exact absurd ((hrun i (by omega) (by omega)).trans (hrun j (by omega) (by omega)).symm)
            hij
        · exact h
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · have := hsize k hk
        omega

open Langlands.LocalFactor.Archimedean ComplexGramFormula in
theorem complexPositionExponent_eq : ∀ (ds : List ComplexCharacterData) (l : ℕ) (hl : l < ds.length),
    complexPositionExponent ds l = (ds[l]).exponent
  | [], _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: ds, l + 1, hl => complexPositionExponent_eq ds l (by simpa using hl)

end Runs

end ComplexSphericalFace

open ComplexStrictLanglandsQuotient ComplexSphericalJacquet ComplexSphericalFace ComplexGramFormula
  ComplexBlockFunctional ComplexBlockFunctionalSized Langlands.LocalFactor.Archimedean

/-- **Cyclicity of the spherical vector with tied blocks.** Let `ks` be a block decomposition with
`BlockOrdered ks t` for the exponents `t` of a list `ds` of complex characters of weight `0`, and
assume `TemperedIrreducibleAt (k + 1)` for every block. Then every `(𝔤𝔩(ℂ), U)`-stable subspace of
the `U`-finite functions of the standard module of `ds` on `GL_{dim ks}(ℂ)` that contains the
spherical vector is everything. -/
theorem complexSphericalBlockCyclic (ks : List ℕ)
    (hU : ∀ k ∈ ks, TemperedIrreducibleAt (k + 1)) (ds : List ComplexCharacterData)
    (hw : ∀ d ∈ ds, d.weight = 0) (hord : BlockOrdered ks (complexPositionExponent ds))
    (f₀ : kFiniteFunctions (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks)))
    (hf₀ : ∀ κ : Matrix.unitaryGroup (Fin (dim ks)) ℂ,
      (f₀ : Langlands.GeneralLinear (dim ks) ℂ → ℂ) (Unitary.toUnits κ) = 1)
    (W : Submodule ℂ (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin (dim ks)) ℂ), ∀ w ∈ W,
      complexStandardRep (dim ks) ds k w ∈ W)
    (hWD : ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ w ∈ W,
      complexStandardLie (dim ks) ds Z w ∈ W)
    (hf₀W : f₀ ∈ W) : W = ⊤ := by
  have hχ := isPhasePower ds
  have h0 : ∀ (l : ℕ) (z : ℂˣ), complexPositionCharacter ds l (phaseUnit z) = 1 := fun l z => by
    rw [complexPositionCharacter_phase, complexPositionWeight_eq_zero ds hw l, zpow_zero]
  by_contra hW'
  obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))), g ∉ W := by
    by_contra hcon
    exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
  have hWX : W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))).subtype ≤ kFiniteFunctions (principalSeries ℂ (dim ks)
      (complexPositionCharacter ds)) (unitaryCompact ℂ (dim ks)) := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hWK' : ∀ k ∈ unitaryCompact ℂ (dim ks), ∀ w ∈ W.map (kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℂ) k w ∈
        W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
          (unitaryCompact ℂ (dim ks))).subtype := by
    intro k hk _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    refine ⟨complexStandardRep (dim ks) ds ⟨(k : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), hk⟩ w,
      hWK _ w hwW, ?_⟩
    change ((complexStandardRep (dim ks) ds _ w : (kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks)))) :
      Langlands.GeneralLinear (dim ks) ℂ → ℂ) = _
    rw [principalSeriesRep_apply_coe]
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), hk⟩ :
        Matrix.unitaryGroup (Fin (dim ks)) ℂ) = k := Units.ext rfl
    rw [hku]
    rfl
  have hWD' : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ w ∈ W.map (kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype,
      rightDerivative (matrixModel ℂ (dim ks)) X w ∈ W.map (kFiniteFunctions
        (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype := by
    intro X _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    exact ⟨complexStandardLie (dim ks) ds (1 ⊗ₜ X) w, hWD _ w hwW,
      principalSeriesLie_one_tmul_apply_coe ℂ (dim ks) (complexPositionCharacter ds) X w⟩
  have hgW' : g ∉ W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))).subtype := by
    rintro ⟨w, hwW, hw⟩
    apply hgW
    have : w = ⟨g, hgS⟩ := Subtype.ext hw
    rw [← this]
    exact hwW
  have hjac := complexBlockFunctionalSized ks hU (complexPositionCharacter ds)
    (complexPositionExponent ds) 0 hχ.eq hχ.one
    (fun l z => by rw [h0, Pi.zero_apply, zpow_zero]) hord _ hWX hWK' hWD' ⟨g, hgS, hgW'⟩
    (f₀ : Langlands.GeneralLinear (dim ks) ℂ → ℂ) ⟨f₀, hf₀W, rfl⟩
  have hK1 : ∀ k ∈ unitaryCompact ℂ (dim ks),
      (f₀ : Langlands.GeneralLinear (dim ks) ℂ → ℂ) k = 1 := fun k hk => by
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), hk⟩ :
        Matrix.unitaryGroup (Fin (dim ks)) ℂ) = k := Units.ext rfl
    rw [← hku]
    exact hf₀ _
  have h1 : (f₀ : Langlands.GeneralLinear (dim ks) ℂ → ℂ) 1 = 1 :=
    hK1 1 (unitaryCompact ℂ (dim ks)).one_mem
  exact jac_ne_zero ks hχ h0 hord f₀.2 (fun k hk => by rw [hK1 k hk, h1])
    (by rw [h1]; exact one_ne_zero) hjac

/-- **Statement (cyclicity of the spherical vector, nonincreasing real parts).** Let `ds` be a list
of `n` complex characters `z ↦ |z|^{2 t_i}` (all weights `0`) whose exponents have nonincreasing
real parts, `Re t_0 ≥ Re t_1 ≥ ⋯`, not all equal. Assume that the complex standard modules with
equal real parts of all sizes `b < n` are irreducible (`TemperedIrreducibleAt b`). Let `f₀` be a
`U(n)`-finite function of the standard module of `ds` equal to `1` on `U(n)` (the spherical
vector). Then every `(𝔤𝔩_n(ℂ), U(n))`-submodule of the `U(n)`-finite functions containing `f₀` is
everything. -/
def ComplexSphericalFaceCyclicStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ b : ℕ, b < n → ComplexBlockFunctionalSized.TemperedIrreducibleAt b) →
    (∀ d ∈ ds, d.weight = 0) →
    ds.Pairwise (fun d e => e.exponent.re ≤ d.exponent.re) →
    (∃ d ∈ ds, ∃ d' ∈ ds, d.exponent.re ≠ d'.exponent.re) →
    ∀ f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
    (∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = 1) →
    ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
      f₀ ∈ W → W = ⊤

theorem complexSphericalFaceCyclic : ComplexSphericalFaceCyclicStatement := by
  intro n ds hn hU hw hord hne f₀ hf₀ W hWK hWD hf₀W
  have hmono : ∀ i j : ℕ, i ≤ j → j < n →
      (complexPositionExponent ds j).re ≤ (complexPositionExponent ds i).re := by
    intro i j hij hj
    rw [complexPositionExponent_eq ds i (by omega), complexPositionExponent_eq ds j (by omega)]
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact List.pairwise_iff_getElem.mp hord i j (by omega) (by omega) hlt
  obtain ⟨ks, hdim, hks, -, hsize⟩ := exists_blocks _ n hmono
  have hne' : ∃ i < n, ∃ j < n,
      (complexPositionExponent ds i).re ≠ (complexPositionExponent ds j).re := by
    obtain ⟨d, hd, d', hd', hdd'⟩ := hne
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
    exact ⟨i, by omega, j, by omega, by
      rwa [complexPositionExponent_eq ds i hi, complexPositionExponent_eq ds j hj]⟩
  subst hdim
  exact complexSphericalBlockCyclic ks (fun k hk => hU (k + 1) (hsize hne' k hk)) ds hw hks f₀ hf₀
    W hWK hWD hf₀W

end Langlands.Archimedean
