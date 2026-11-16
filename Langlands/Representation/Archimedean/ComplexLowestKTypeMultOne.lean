import Langlands.Representation.RankinSelberg.FiniteCauchyBinet
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexPartialJacquet
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Multiplicity one of minor-monomial `U(n)`-types in complex principal series

Let `f₀` be a `U(n)`-finite function of the principal series of `χ` on `GL_n(ℂ)` whose
restriction to `U(n)` is the minor monomial `κ ↦ det(κ)^d ∏_j Δ_{j+1}(κ)^{c_j}`, where
`Δ_{j+1}(κ)` is the minor on the bottom `j + 1` rows and the first `j + 1` columns. Every
`U(n)`-equivariant endomorphism `E` maps `f₀` to a multiple of `f₀`
(`ComplexLowestKType.exists_smul_of_minorMonomial`, `ComplexLowestKTypeMultOneStatement`).

The proof averages right translates over the finite group of `D_{ζ^t}`,
`D_s = diag(s^{n-1}, …, s, 1)`, `ζ` a primitive `N`-th root of unity with `N` large. By
Cauchy–Binet, `Δ_{j+1}(A D_s C)` is `s^{e_j}` times a polynomial in `s` whose value at `0` is a
product of minors of `A` and `C`; the roots-of-unity filter keeps only that constant term. With
`ComplexTemperedComplement.complexTemperedCyclicVector` this gives irreducibility of a tempered
standard module from cyclicity of such an `f₀` (`complexTemperedIrreducible_of_minorMonomial`).
-/

noncomputable section

open Matrix Polynomial Finset

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexLowestKType

variable {n : ℕ}

/-! ## Minors -/

/-- The bottom `j + 1` indices `n - (j + 1), …, n - 1` of `Fin n`, in increasing order. -/
def botIdx (j : Fin n) (i : Fin (j + 1)) : Fin n :=
  ⟨n - (j + 1) + i, by have := j.isLt; have := i.isLt; omega⟩

/-- The first `j + 1` indices `0, …, j` of `Fin n`. -/
def topIdx (j : Fin n) (i : Fin (j + 1)) : Fin n :=
  ⟨i, by have := j.isLt; have := i.isLt; omega⟩

theorem botIdx_strictMono (j : Fin n) : StrictMono (botIdx j) := fun a b h => by
  rw [Fin.lt_def] at h ⊢
  simp only [botIdx]
  omega

/-- `Δ_{j+1}(g)`: the minor of `g` on the bottom `j + 1` rows and the first `j + 1` columns. -/
def minor (j : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (botIdx j) (topIdx j)).det

/-- The minor of `g` on the bottom `j + 1` rows and the last `j + 1` columns. -/
def lowMinor (j : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (botIdx j) (botIdx j)).det

/-- The minor monomial `det(g)^d ∏_j Δ_{j+1}(g)^{c_j}`. -/
def minorMonomial (c : Fin n → ℕ) (d : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  g.det ^ d * ∏ j, minor j g ^ c j

/-- The monomial `det(g)^d ∏_j (lowMinor j g)^{c_j}` in the minors on the last columns. -/
def lowMonomial (c : Fin n → ℕ) (d : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  g.det ^ d * ∏ j, lowMinor j g ^ c j

/-! ## The one-parameter torus `D_s = diag(s^{n-1}, …, s, 1)` -/

/-- The exponents `a_i = n - 1 - i`. -/
def wt (i : Fin n) : ℕ := n - 1 - i

/-- `D_s = diag(s^{n-1}, …, s, 1)`. -/
def torus (s : ℂ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => s ^ wt i

/-- The bottom `j + 1` indices as a finset. -/
def bot (j : Fin n) : Finset (Fin n) :=
  univ.map ⟨botIdx j, (botIdx_strictMono j).injective⟩

theorem card_bot (j : Fin n) : (bot j).card = j + 1 := by
  simp [bot]

theorem mem_bot {j i : Fin n} : i ∈ bot j ↔ n - (j + 1) ≤ (i : ℕ) := by
  have hj := j.isLt
  have hi := i.isLt
  simp only [bot, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨t, rfl⟩
    simp [botIdx]
  · intro h
    refine ⟨⟨i - (n - (j + 1)), by omega⟩, ?_⟩
    ext
    simp only [botIdx]
    omega

theorem botIdx_mem_bot (j : Fin n) (t : Fin (j + 1)) : botIdx j t ∈ bot j := by
  rw [mem_bot]
  simp [botIdx]

theorem orderEmbOfFin_bot (j : Fin n) :
    ((bot j).orderEmbOfFin (card_bot j) : Fin (j + 1) → Fin n) = botIdx j :=
  (orderEmbOfFin_unique (card_bot j) (botIdx_mem_bot j) (botIdx_strictMono j)).symm

/-- `e_j = ∑_{i ∈ bot j} a_i`, the lowest power of `s` in `Δ_{j+1}(A D_s C)`. -/
def lowExp (j : Fin n) : ℕ := ∑ i ∈ bot j, wt i

theorem lowExp_eq (j : Fin n) : lowExp j = ∑ t : Fin (j + 1), wt (botIdx j t) := by
  rw [lowExp, bot, sum_map]
  rfl

/-- The exponent of every other Cauchy–Binet term exceeds `e_j` by at least `|S \ bot j|`. -/
theorem exp_bound (j : Fin n) (S : Finset (Fin n)) (hS : S.card = j + 1) :
    lowExp j + (S \ bot j).card ≤ ∑ i ∈ S, wt i := by
  classical
  have hj := j.isLt
  have h1 := sum_inter_add_sum_sdiff S (bot j) wt
  have h2 := sum_inter_add_sum_sdiff (bot j) S wt
  have hcard : (S \ bot j).card = (bot j \ S).card :=
    card_sdiff_comm (by rw [hS, card_bot])
  have hlo : (S \ bot j).card • (j + 1 : ℕ) ≤ ∑ i ∈ S \ bot j, wt i := by
    refine card_nsmul_le_sum _ _ _ fun i hi => ?_
    have hi' := (mem_sdiff.mp hi).2
    rw [mem_bot] at hi'
    have := i.isLt
    simp only [wt]
    omega
  have hhi : ∑ i ∈ bot j \ S, wt i ≤ (bot j \ S).card • (j : ℕ) := by
    refine sum_le_card_nsmul _ _ _ fun i hi => ?_
    have hi' := (mem_sdiff.mp hi).1
    rw [mem_bot] at hi'
    have := i.isLt
    simp only [wt]
    omega
  rw [smul_eq_mul] at hlo hhi
  rw [inter_comm] at h2
  rw [lowExp, ← h2, ← h1]
  rw [hcard] at hlo ⊢
  nlinarith

/-! ## Cauchy–Binet expansion of `Δ_{j+1}(A D_s C)` -/

/-- The Cauchy–Binet coefficient of the column set `S`. -/
def coef (A C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (S : {S : Finset (Fin n) // S.card = j + 1}) : ℂ :=
  (A.submatrix (botIdx j) (S.val.orderEmbOfFin S.property)).det *
    (C.submatrix (S.val.orderEmbOfFin S.property) (topIdx j)).det

theorem minor_mul_torus_mul (A C : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (j : Fin n) :
    minor j (A * torus s * C) = ∑ S : {S : Finset (Fin n) // S.card = j + 1},
      coef A C j S * s ^ (∑ i ∈ S.val, wt i) := by
  have hsplit : (A * torus s * C).submatrix (botIdx j) (topIdx j) =
      (A.submatrix (botIdx j) id * torus s) * C.submatrix id (topIdx j) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [minor, hsplit, Langlands.GeneralLinear.Spherical.det_rectangular_mul]
  refine sum_congr rfl fun S _ => ?_
  have hsub : (A.submatrix (botIdx j) id * torus s).submatrix id
      (S.val.orderEmbOfFin S.property) =
      A.submatrix (botIdx j) (S.val.orderEmbOfFin S.property) *
        diagonal (fun t => s ^ wt (S.val.orderEmbOfFin S.property t)) := by
    ext a b
    simp [torus, Matrix.mul_diagonal]
  rw [hsub, det_mul, det_diagonal, coef, prod_pow_eq_pow_sum]
  have hsum : ∑ t, wt (S.val.orderEmbOfFin S.property t) = ∑ i ∈ S.val, wt i := by
    conv_rhs => rw [← map_orderEmbOfFin_univ S.val S.property, sum_map]
    rfl
  rw [hsum, Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id]
  ring

/-- `R_j = ∑_S coef_S X^{σ(S) - e_j}`, with `σ(S) = ∑_{i ∈ S} a_i`. -/
def redPoly (A C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ℂ[X] :=
  ∑ S : {S : Finset (Fin n) // S.card = j + 1},
    Polynomial.C (coef A C j S) * X ^ (∑ i ∈ S.val, wt i - lowExp j)

theorem minor_eq_eval (A C : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (j : Fin n) :
    minor j (A * torus s * C) = s ^ lowExp j * (redPoly A C j).eval s := by
  rw [minor_mul_torus_mul, redPoly, eval_finsetSum, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  have hle : lowExp j ≤ ∑ i ∈ S.val, wt i :=
    le_trans (Nat.le_add_right _ _) (exp_bound j S.val S.property)
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hle]

theorem eval_zero_redPoly (A C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (redPoly A C j).eval 0 = lowMinor j A * minor j C := by
  classical
  rw [redPoly, eval_finsetSum, sum_eq_single ⟨bot j, card_bot j⟩]
  · simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [lowExp, Nat.sub_self, pow_zero, mul_one, coef]
    simp only
    rw [orderEmbOfFin_bot]
    rfl
  · intro S _ hS
    have hne : S.val ≠ bot j := fun h => hS (Subtype.ext h)
    have hpos : 0 < (S.val \ bot j).card := by
      rw [card_pos]
      by_contra hem
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hem
      exact hne (eq_of_subset_of_card_le hem (by rw [S.property, card_bot]))
    have hb := exp_bound j S.val S.property
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (mem_univ _) h

theorem natDegree_redPoly_le (A C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (redPoly A C j).natDegree ≤ n * n := by
  refine natDegree_sum_le_of_forall_le _ _ fun S _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  refine (Nat.sub_le _ _).trans ?_
  have h1 : ∑ i ∈ S.val, wt i ≤ S.val.card • n :=
    sum_le_card_nsmul _ _ _ fun i _ => by simp only [wt]; omega
  have h2 : S.val.card ≤ n := by
    simpa using card_le_univ S.val
  rw [smul_eq_mul] at h1
  nlinarith

/-- `∑_j e_j c_j`. -/
def totExp (c : Fin n → ℕ) : ℕ := ∑ j, lowExp j * c j

/-- The product `Q = ∏_j R_j^{c_j}`. -/
def prodPoly (c : Fin n → ℕ) (A C : Matrix (Fin n) (Fin n) ℂ) : ℂ[X] :=
  ∏ j, redPoly A C j ^ c j

theorem natDegree_prodPoly_le (c : Fin n → ℕ) (A C : Matrix (Fin n) (Fin n) ℂ) :
    (prodPoly c A C).natDegree ≤ ∑ j, c j * (n * n) := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) (sum_le_sum fun j _ => ?_)
  exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_redPoly_le A C j))

theorem eval_zero_prodPoly (c : Fin n → ℕ) (A C : Matrix (Fin n) (Fin n) ℂ) :
    (prodPoly c A C).eval 0 = ∏ j, (lowMinor j A * minor j C) ^ c j := by
  simp only [prodPoly, eval_prod, eval_pow, eval_zero_redPoly]

theorem minorMonomial_mul_torus_mul (c : Fin n → ℕ) (d : ℤ) (A C : Matrix (Fin n) (Fin n) ℂ)
    (s : ℂ) :
    minorMonomial c d (A * torus s * C) =
      A.det ^ d * C.det ^ d * ((torus s : Matrix (Fin n) (Fin n) ℂ).det ^ d * s ^ totExp c) *
        (prodPoly c A C).eval s := by
  simp only [minorMonomial, det_mul, mul_zpow, minor_eq_eval, mul_pow, prod_mul_distrib,
    prodPoly, eval_prod, eval_pow, ← pow_mul, prod_pow_eq_pow_sum, totExp]
  ring

theorem minor_torus_mul (C : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (j : Fin n) :
    minor j (torus s * C) = s ^ lowExp j * minor j C := by
  have h : (torus s * C).submatrix (botIdx j) (topIdx j) =
      diagonal (fun t => s ^ wt (botIdx j t)) * C.submatrix (botIdx j) (topIdx j) := by
    ext a b
    simp [torus, Matrix.diagonal_mul]
  rw [minor, h, det_mul, det_diagonal, prod_pow_eq_pow_sum, lowExp_eq, minor]

theorem minorMonomial_torus_mul (c : Fin n → ℕ) (d : ℤ) (C : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    minorMonomial c d (torus s * C) =
      ((torus s : Matrix (Fin n) (Fin n) ℂ).det ^ d * s ^ totExp c) * minorMonomial c d C := by
  simp only [minorMonomial, det_mul, mul_zpow, minor_torus_mul, mul_pow, prod_mul_distrib,
    ← pow_mul, prod_pow_eq_pow_sum, totExp]
  ring

/-! ## The roots-of-unity filter -/

theorem sum_eval_rootsOfUnity {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {Q : ℂ[X]}
    (hQ : Q.natDegree < N) :
    ∑ t ∈ range N, Q.eval (ζ ^ t) = N * Q.coeff 0 := by
  simp_rw [eval_eq_sum_range' hQ]
  rw [sum_comm, sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [← mul_sum]
    have hne : ζ ^ i ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hi0 (mem_range.mp hi)
    have hgeom : ∑ t ∈ range N, (ζ ^ t) ^ i = 0 := by
      have : ∀ t, (ζ ^ t) ^ i = (ζ ^ i) ^ t := fun t => by rw [← pow_mul, ← pow_mul, mul_comm]
      simp_rw [this]
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
        zero_div]
    rw [hgeom, mul_zero]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-- The weight `w(s) = det(D_s)^d s^{∑_j e_j c_j}` of the minor monomial under `D_s`. -/
def wgt (c : Fin n → ℕ) (d : ℤ) (s : ℂ) : ℂ :=
  (torus s : Matrix (Fin n) (Fin n) ℂ).det ^ d * s ^ totExp c

theorem wgt_ne_zero (c : Fin n → ℕ) (d : ℤ) {s : ℂ} (hs : s ≠ 0) : wgt c d s ≠ 0 := by
  have h : (torus s : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    rw [torus, det_diagonal]
    exact prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hs
  exact mul_ne_zero (zpow_ne_zero _ h) (pow_ne_zero _ hs)

/-- **The averaging identity.** For a primitive `N`-th root of unity `ζ` with `N` larger than
the degree bound `∑_j c_j n²`,
`∑_{t < N} w(ζ^t)⁻¹ M(A D_{ζ^t} C) = N · M_low(A) · M(C)`, where `M` is the minor monomial and
`M_low` the monomial in the minors on the last columns. -/
theorem sum_minorMonomial (c : Fin n → ℕ) (d : ℤ) (A C : Matrix (Fin n) (Fin n) ℂ) {N : ℕ}
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : ∑ j, c j * (n * n) < N) :
    ∑ t ∈ range N, (wgt c d (ζ ^ t))⁻¹ * minorMonomial c d (A * torus (ζ ^ t) * C) =
      N * (lowMonomial c d A * minorMonomial c d C) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hterm : ∀ t ∈ range N,
      (wgt c d (ζ ^ t))⁻¹ * minorMonomial c d (A * torus (ζ ^ t) * C) =
        A.det ^ d * C.det ^ d * (prodPoly c A C).eval (ζ ^ t) := by
    intro t _
    rw [minorMonomial_mul_torus_mul]
    change (wgt c d (ζ ^ t))⁻¹ * (_ * _ * wgt c d (ζ ^ t) * _) = _
    rw [mul_comm (_ * _) (wgt c d (ζ ^ t)), mul_assoc (wgt c d (ζ ^ t)),
      inv_mul_cancel_left₀ (wgt_ne_zero c d (pow_ne_zero t hζ0))]
  rw [sum_congr rfl hterm, ← mul_sum,
    sum_eval_rootsOfUnity hζ ((natDegree_prodPoly_le c A C).trans_lt hN),
    coeff_zero_eq_eval_zero, eval_zero_prodPoly]
  simp only [lowMonomial, minorMonomial, mul_pow, prod_mul_distrib]
  ring

/-! ## The averaging operator on the principal series -/

section Representation

open ComplexPrincipalSeriesExtension ComplexGramFormula

variable {χ : ℕ → ℂˣ → ℂ}

theorem ne_zero_of_norm_eq_one {s : ℂ} (hs : ‖s‖ = 1) : s ≠ 0 := by
  rintro rfl
  rw [norm_zero] at hs
  exact zero_ne_one hs

/-- The entries `s^{a_i}` of `D_s`, as units, for `|s| = 1`. -/
def torusUnit (s : ℂ) (hs : ‖s‖ = 1) (i : Fin n) : ℂˣ :=
  Units.mk0 (s ^ wt i) (pow_ne_zero _ (ne_zero_of_norm_eq_one hs))

/-- `D_s` as an element of `U(n)`, for `|s| = 1`. -/
def torusU (s : ℂ) (hs : ‖s‖ = 1) : Matrix.unitaryGroup (Fin n) ℂ :=
  phaseMatrix (torusUnit s hs)

theorem coe_torusU (s : ℂ) (hs : ‖s‖ = 1) :
    ((torusU s hs : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = torus s := by
  rw [torusU, phaseMatrix_val, torus]
  congr 1
  funext i
  rw [phaseUnit_val, torusUnit, Units.val_mk0, norm_pow, hs, one_pow, Complex.ofReal_one,
    div_one]

variable (χ) in
/-- The value of the character of the principal series of `χ` at `D_s`. -/
def torusChar (s : ℂ) (hs : ‖s‖ = 1) : ℂ :=
  principalSeriesCharacter ℂ n χ fun i => phaseUnit (torusUnit s hs i)

theorem apply_torusU_mul {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    (s : ℂ) (hs : ‖s‖ = 1) (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    f (Unitary.toUnits (torusU s hs * κ)) = torusChar (n := n) χ s hs * f (Unitary.toUnits κ) := by
  rw [torusU, ComplexPartialJacquet.phaseMatrix_toUnits]
  exact hf.2 _ _ _

theorem coe_unitary_mul (a b : Matrix.unitaryGroup (Fin n) ℂ) :
    ((a * b : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (a : Matrix (Fin n) (Fin n) ℂ) * (b : Matrix (Fin n) (Fin n) ℂ) :=
  rfl

/-- A nonzero function of the principal series restricting to a minor monomial on `U(n)`
determines the character at `D_s`: `χ(D_s) = w(s)`. -/
theorem torusChar_eq {f₀ : Langlands.GeneralLinear n ℂ → ℂ} (hf₀ : f₀ ∈ principalSeries ℂ n χ)
    (c : Fin n → ℕ) (d : ℤ)
    (hmin : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      f₀ (Unitary.toUnits κ) = minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ))
    {κ₁ : Matrix.unitaryGroup (Fin n) ℂ} (hκ₁ : f₀ (Unitary.toUnits κ₁) ≠ 0)
    (s : ℂ) (hs : ‖s‖ = 1) :
    torusChar (n := n) χ s hs = wgt c d s := by
  have h1 := apply_torusU_mul hf₀ s hs κ₁
  rw [hmin, hmin, coe_unitary_mul, coe_torusU, minorMonomial_torus_mul] at h1
  rw [hmin] at hκ₁
  exact (mul_right_cancel₀ hκ₁ h1).symm

/-- The `U(n)`-finite functions of the principal series of `χ`. -/
abbrev KX (n : ℕ) (χ : ℕ → ℂˣ → ℂ) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)

theorem rep_rep_apply (k κ : Matrix.unitaryGroup (Fin n) ℂ) (f : KX n χ)
    (x : Langlands.GeneralLinear n ℂ) :
    ((principalSeriesRep ℂ n χ k (principalSeriesRep ℂ n χ κ f) : KX n χ) :
        Langlands.GeneralLinear n ℂ → ℂ) x =
      (f : Langlands.GeneralLinear n ℂ → ℂ) (x * Unitary.toUnits (k * κ)) := by
  show (f : Langlands.GeneralLinear n ℂ → ℂ) (x * Unitary.toUnits k * Unitary.toUnits κ) = _
  rw [map_mul, mul_assoc]

variable (χ) in
/-- The averaged translate `∑_{t < N} w_t⁻¹ ρ(D_{ζ^t}) ρ(κ) f`. -/
def avg (N : ℕ) (ζ : ℂ) (hζ : ∀ t : ℕ, ‖ζ ^ t‖ = 1) (w : ℕ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (f : KX n χ) : KX n χ :=
  ∑ t ∈ range N, (w t)⁻¹ •
    principalSeriesRep ℂ n χ (torusU (ζ ^ t) (hζ t)) (principalSeriesRep ℂ n χ κ f)

theorem avg_apply (N : ℕ) (ζ : ℂ) (hζ : ∀ t : ℕ, ‖ζ ^ t‖ = 1) (w : ℕ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (f : KX n χ) (x : Langlands.GeneralLinear n ℂ) :
    (avg χ N ζ hζ w κ f : Langlands.GeneralLinear n ℂ → ℂ) x =
      ∑ t ∈ range N, (w t)⁻¹ *
        (f : Langlands.GeneralLinear n ℂ → ℂ) (x * Unitary.toUnits (torusU (ζ ^ t) (hζ t) * κ)) := by
  rw [avg, Submodule.coe_sum, Finset.sum_apply]
  refine sum_congr rfl fun t _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, rep_rep_apply]

theorem map_avg (E : KX n χ →ₗ[ℂ] KX n χ)
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      E (principalSeriesRep ℂ n χ k f) = principalSeriesRep ℂ n χ k (E f))
    (N : ℕ) (ζ : ℂ) (hζ : ∀ t : ℕ, ‖ζ ^ t‖ = 1) (w : ℕ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (f : KX n χ) :
    E (avg χ N ζ hζ w κ f) = avg χ N ζ hζ w κ (E f) := by
  simp only [avg, map_sum, map_smul, hE]

theorem toUnits_coe_mem {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ : Matrix.unitaryGroup (Fin n) ℂ) = k :=
  Units.ext rfl

/-- **Multiplicity one of a minor-monomial `U(n)`-type.** Let `f₀` be a `U(n)`-finite function
of the principal series of `χ` whose restriction to `U(n)` is the minor monomial
`κ ↦ det(κ)^d ∏_j Δ_{j+1}(κ)^{c_j}`. Then every `U(n)`-equivariant endomorphism maps `f₀` to a
multiple of itself. -/
theorem exists_smul_of_minorMonomial (c : Fin n → ℕ) (d : ℤ) (f₀ : KX n χ)
    (hmin : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) =
        minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ))
    (E : KX n χ →ₗ[ℂ] KX n χ)
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      E (principalSeriesRep ℂ n χ k f) = principalSeriesRep ℂ n χ k (E f)) :
    ∃ a : ℂ, E f₀ = a • f₀ := by
  by_cases h0 : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = 0
  · have hf : f₀ = 0 := by
      refine Subtype.ext (eq_of_eqOn_unitary f₀.2.1 (Submodule.zero_mem _) fun k hk => ?_)
      rw [← toUnits_coe_mem hk, h0]
      rfl
    exact ⟨0, by rw [hf, map_zero, smul_zero]⟩
  push Not at h0
  obtain ⟨κ₁, hκ₁⟩ := h0
  set N : ℕ := ∑ j, c j * (n * n) + 1 with hNdef
  have hN0 : N ≠ 0 := by omega
  have hNlt : ∑ j, c j * (n * n) < N := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN0
  have hζn : ∀ t : ℕ, ‖ζ ^ t‖ = 1 := fun t => by rw [norm_pow, hζ.norm'_eq_one hN0, one_pow]
  set w : ℕ → ℂ := fun t => wgt c d (ζ ^ t) with hwdef
  have hchar : ∀ t : ℕ, torusChar (n := n) χ (ζ ^ t) (hζn t) = w t := fun t =>
    torusChar_eq f₀.2.1 c d hmin hκ₁ _ _
  -- averaging recovers `N f(κ)` at the identity
  have hv1 : ∀ (κ : Matrix.unitaryGroup (Fin n) ℂ) (f : KX n χ),
      (avg χ N ζ hζn w κ f : Langlands.GeneralLinear n ℂ → ℂ) 1 =
        N * (f : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) := by
    intro κ f
    rw [avg_apply]
    have hterm : ∀ t ∈ range N, (w t)⁻¹ * (f : Langlands.GeneralLinear n ℂ → ℂ)
        (1 * Unitary.toUnits (torusU (ζ ^ t) (hζn t) * κ)) =
          (f : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) := by
      intro t _
      rw [one_mul, apply_torusU_mul f.2.1, hchar,
        inv_mul_cancel_left₀ (wgt_ne_zero c d (pow_ne_zero t hζ0))]
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  -- averaging `f₀` gives `N M_low(k) f₀(κ)` on `U(n)`
  have hvK : ∀ (κ k : Matrix.unitaryGroup (Fin n) ℂ),
      (avg χ N ζ hζn w κ f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
        N * (lowMonomial c d (k : Matrix (Fin n) (Fin n) ℂ) *
          (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ)) := by
    intro κ k
    rw [avg_apply, hmin κ]
    have hterm : ∀ t ∈ range N, (w t)⁻¹ * (f₀ : Langlands.GeneralLinear n ℂ → ℂ)
        (Unitary.toUnits k * Unitary.toUnits (torusU (ζ ^ t) (hζn t) * κ)) =
          (wgt c d (ζ ^ t))⁻¹ * minorMonomial c d
            ((k : Matrix (Fin n) (Fin n) ℂ) * torus (ζ ^ t) * (κ : Matrix (Fin n) (Fin n) ℂ)) := by
      intro t _
      rw [← map_mul, hmin, coe_unitary_mul, coe_unitary_mul, coe_torusU, ← Matrix.mul_assoc]
    rw [sum_congr rfl hterm, sum_minorMonomial c d _ _ hζ hNlt]
  -- the averages of the translates of `f₀` are proportional
  have hprop : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      avg χ N ζ hζn w κ f₀ =
        ((f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) /
          (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ₁)) • avg χ N ζ hζn w κ₁ f₀ := by
    intro κ
    refine Subtype.ext (eq_of_eqOn_unitary (avg χ N ζ hζn w κ f₀).2.1
      (_ • avg χ N ζ hζn w κ₁ f₀).2.1 fun k hk => ?_)
    rw [← toUnits_coe_mem hk, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hvK, hvK]
    field_simp
  -- conclusion
  have hg : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (E f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) =
        (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) /
          (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ₁) *
          (E f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ₁) := by
    intro κ
    have h := congrArg (fun F : KX n χ => (F : Langlands.GeneralLinear n ℂ → ℂ) 1)
      (congrArg E (hprop κ))
    simp only [map_smul, map_avg E hE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hv1] at h
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    calc (E f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ)
        = (N : ℂ)⁻¹ * (N * (E f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ)) := by
          rw [inv_mul_cancel_left₀ hN]
      _ = _ := by rw [h]; field_simp
  refine ⟨(E f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ₁) /
    (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ₁), ?_⟩
  refine Subtype.ext (eq_of_eqOn_unitary (E f₀).2.1 (_ • f₀).2.1 fun k hk => ?_)
  rw [← toUnits_coe_mem hk, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hg]
  field_simp

end Representation

end ComplexLowestKType

open ComplexLowestKType Langlands.LocalFactor.Archimedean
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Multiplicity one of the minor-monomial `U(n)`-types of complex standard modules.**
Let `ds` be a list of complex characters, `c : Fin n → ℕ` and `d : ℤ`, and let `f₀` be a
`U(n)`-finite function of `complexStandardModule n ds` whose restriction to `U(n)` is the minor
monomial `κ ↦ det(κ)^d ∏_{j < n} Δ_{j+1}(κ)^{c_j}`, where `Δ_{j+1}(κ)` is the minor of `κ` on the
bottom `j + 1` rows and the first `j + 1` columns. Then every `U(n)`-equivariant linear
endomorphism of the `U(n)`-finite functions maps `f₀` to a multiple of `f₀`. -/
def ComplexLowestKTypeMultOneStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (c : Fin n → ℕ) (d : ℤ)
    (f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
    (∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) =
        minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ)) →
    ∀ E : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
        E (complexStandardRep n ds k f) = complexStandardRep n ds k (E f)) →
      ∃ a : ℂ, E f₀ = a • f₀

theorem complexLowestKTypeMultOne : ComplexLowestKTypeMultOneStatement :=
  fun _ _ c d f₀ hmin E hE => exists_smul_of_minorMonomial c d f₀ hmin E hE

/-- **Irreducibility from a cyclic minor-monomial vector.** Let `ds` be a list of `n` complex
characters whose exponents all have the same real part, and let `f₀ ≠ 0` be a `U(n)`-finite
function of `complexStandardModule n ds` restricting on `U(n)` to a minor monomial. If every
`(𝔤𝔩_n(ℂ), U(n))`-submodule containing `f₀` is everything, the module is irreducible. -/
theorem complexTemperedIrreducible_of_minorMonomial (n : ℕ) (ds : List ComplexCharacterData)
    (hlen : ds.length = n) (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    (c : Fin n → ℕ) (d : ℤ)
    (f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) (hf₀ : f₀ ≠ 0)
    (hmin : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) =
        minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ))
    (hcyc : ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
      f₀ ∈ W → W = ⊤) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) :=
  complexTemperedCyclicVector n ds hlen htemp f₀ hf₀ hcyc fun E hE =>
    complexLowestKTypeMultOne n ds c d f₀ hmin E hE

end Langlands.Archimedean
