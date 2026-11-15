import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Subalgebra

/-!
# Complex principal series have nonzero `U(n)`-finite vectors

`complexStandardNontrivial` proves `ComplexStandardNontrivialStatement`: for every `n` and every
list `ds` of `n` complex characters, the `U(n)`-finite functions of
`complexStandardModule n ds` form a nontrivial space.

The function is written down explicitly. For `0 ≤ k < n` let `D_k(g)` be the bottom-right
minor `det (g i j)_{i, j ≥ k}` and `G_k(g) = det (R Rᴴ)` the Gram determinant of the rows
`R = (g i j)_{i ≥ k}` of `g`. Then

`f(g) = ∏ₖ D_k(g)^(p_k) conj(D_k(g))^(q_k) G_k(g)^(σ_k)`,

with integers `p_k, q_k ≥ 0` and complex `σ_k` read off from successive differences of the
weights and exponents of the characters. Left multiplication by an upper triangular `b`
multiplies `D_k` by `∏_{i ≥ k} b i i` and `G_k` by its squared absolute value, which gives
the transformation law of the principal series; right multiplication by a unitary matrix
leaves every `G_k` unchanged, and the `U(n)`-translates of `D_k` and `conj D_k` stay in the
polynomials in the matrix entries and their conjugates, which gives `U(n)`-finiteness;
`f(1) = 1`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator ComplexOrder

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

/-! ## `K`-finite functions form a subalgebra -/

section Subalgebra

variable {G : Type*} [Group G] (K : Subgroup G)

theorem rightTranslation_mul_apply (k : G) (f h : G → ℂ) :
    Whittaker.rightTranslation ℂ G k (f * h) =
      Whittaker.rightTranslation ℂ G k f * Whittaker.rightTranslation ℂ G k h :=
  rfl

/-- The `K`-finite functions on `G` for right translation form a subalgebra of all functions. -/
def kFiniteSubalgebra : Subalgebra ℂ (G → ℂ) where
  carrier := kFiniteVectors (Whittaker.rightTranslation ℂ G) K
  mul_mem' {f h} hf hh := by
    change f * h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K
    change f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K at hf
    change h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K at hh
    rw [mem_kFiniteVectors_iff] at hf hh ⊢
    have hle : Submodule.span ℂ (Set.range fun k : K =>
          Whittaker.rightTranslation ℂ G (k : G) (f * h)) ≤
        Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ G (k : G) f) *
          Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ G (k : G) h) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show Whittaker.rightTranslation ℂ G (k : G) (f * h) ∈ (_ : Submodule ℂ (G → ℂ))
      rw [rightTranslation_mul_apply]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩)
        (Submodule.subset_span ⟨k, rfl⟩)
    have hfg : (Submodule.span ℂ (Set.range fun k : K =>
          Whittaker.rightTranslation ℂ G (k : G) f) *
        Submodule.span ℂ (Set.range fun k : K =>
          Whittaker.rightTranslation ℂ G (k : G) h)).FG :=
      (Module.Finite.iff_fg.mp hf).mul (Module.Finite.iff_fg.mp hh)
    have := Module.Finite.iff_fg.mpr hfg
    exact Submodule.finiteDimensional_of_le hle
  add_mem' hf hh := (kFiniteVectors (Whittaker.rightTranslation ℂ G) K).add_mem hf hh
  algebraMap_mem' c := by
    change algebraMap ℂ (G → ℂ) c ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K
    rw [mem_kFiniteVectors_iff]
    have hle : Submodule.span ℂ (Set.range fun k : K =>
          Whittaker.rightTranslation ℂ G (k : G) (algebraMap ℂ (G → ℂ) c)) ≤
        Submodule.span ℂ {algebraMap ℂ (G → ℂ) c} := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span rfl
    exact Submodule.finiteDimensional_of_le hle

theorem mem_kFiniteSubalgebra_iff (f : G → ℂ) :
    f ∈ kFiniteSubalgebra K ↔ f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K :=
  Iff.rfl

/-- A function invariant under right translation by `K` is `K`-finite. -/
theorem mem_kFiniteSubalgebra_of_invariant {f : G → ℂ}
    (hf : ∀ k ∈ K, Whittaker.rightTranslation ℂ G k f = f) : f ∈ kFiniteSubalgebra K := by
  rw [mem_kFiniteSubalgebra_iff, mem_kFiniteVectors_iff]
  have hle : Submodule.span ℂ (Set.range fun k : K =>
        Whittaker.rightTranslation ℂ G (k : G) f) ≤ Submodule.span ℂ {f} := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show Whittaker.rightTranslation ℂ G (k : G) f ∈ (_ : Submodule ℂ (G → ℂ))
    rw [hf k k.2]
    exact Submodule.subset_span rfl
  exact Submodule.finiteDimensional_of_le hle

/-- A function whose right translates by `K` lie in a finite-dimensional space is `K`-finite. -/
theorem mem_kFiniteSubalgebra_of_le {f : G → ℂ} (S : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ S] (hf : ∀ k ∈ K, Whittaker.rightTranslation ℂ G k f ∈ S) :
    f ∈ kFiniteSubalgebra K := by
  rw [mem_kFiniteSubalgebra_iff, mem_kFiniteVectors_iff]
  have hle : Submodule.span ℂ (Set.range fun k : K =>
        Whittaker.rightTranslation ℂ G (k : G) f) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hf k k.2
  exact Submodule.finiteDimensional_of_le hle

/-- The determinant of a matrix with entries in a subalgebra lies in the subalgebra. -/
theorem det_mem_subalgebra {A : Type*} [CommRing A] [Algebra ℂ A] (S : Subalgebra ℂ A)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (hM : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  let M' : Matrix ι ι S := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have h : M = (S.val : S →+* A).mapMatrix M' := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det]
  exact (M'.det).2

end Subalgebra

/-! ## Bottom rows, bottom-right minors and Gram determinants -/

section Minors

variable {n : ℕ}

/-- The indices `i : Fin n` with `k ≤ i`. -/
abbrev LowIdx (n k : ℕ) := {i : Fin n // k ≤ (i : ℕ)}

/-- The bottom-right minor `det (Y i j)_{i, j ≥ k}`. -/
def lowMinor (k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (Y.submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val).det

/-- The Gram determinant `det (R Rᴴ)` of the rows `R = (Y i j)_{i ≥ k}` of `Y`. -/
def lowGram (k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (Y.submatrix (Subtype.val : LowIdx n k → Fin n) id *
    (Y.submatrix (Subtype.val : LowIdx n k → Fin n) id)ᴴ).det

/-- The rows `i ≥ k` of `b Y`, for `b` upper triangular, are `b' R` with `b'` the bottom-right
block of `b` and `R` the rows `i ≥ k` of `Y`. -/
theorem lowRows_mul_of_isUpperTriangular (k : ℕ) {ι : Type*} (c : ι → Fin n)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (b * Y).submatrix (Subtype.val : LowIdx n k → Fin n) c =
      b.submatrix Subtype.val Subtype.val * Y.submatrix (Subtype.val : LowIdx n k → Fin n) c := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun l : Fin n => k ≤ (l : ℕ))]
  have h0 : ∑ l : {l : Fin n // ¬ k ≤ (l : ℕ)}, b i.1 l.1 * Y l.1 (c j) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hlt : l.1 < i.1 := by
      have h1 := l.2
      have h2 := i.2
      show (l.1 : ℕ) < (i.1 : ℕ)
      omega
    rw [hb hlt, zero_mul]
  rw [h0, add_zero]

theorem det_lowBlock_of_isUpperTriangular (k : ℕ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsUpperTriangular) :
    (b.submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val).det =
      ∏ i : LowIdx n k, b i.1 i.1 := by
  have h : (b.submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val).IsUpperTriangular :=
    fun i j hij => hb hij
  rw [Matrix.det_of_isUpperTriangular h]
  rfl

theorem lowMinor_mul_of_isUpperTriangular (k : ℕ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsUpperTriangular) (Y : Matrix (Fin n) (Fin n) ℂ) :
    lowMinor k (b * Y) = (∏ i : LowIdx n k, b i.1 i.1) * lowMinor k Y := by
  rw [lowMinor, lowRows_mul_of_isUpperTriangular k Subtype.val hb, Matrix.det_mul,
    det_lowBlock_of_isUpperTriangular k hb]
  rfl

theorem lowGram_mul_of_isUpperTriangular (k : ℕ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsUpperTriangular) (Y : Matrix (Fin n) (Fin n) ℂ) :
    lowGram k (b * Y) =
      (Complex.normSq (∏ i : LowIdx n k, b i.1 i.1) : ℂ) * lowGram k Y := by
  rw [lowGram, lowRows_mul_of_isUpperTriangular k id hb, Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_assoc (b.submatrix _ _), Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, det_lowBlock_of_isUpperTriangular k hb, ← Complex.mul_conj]
  simp only [lowGram, Complex.star_def]
  ring

theorem lowGram_mul_unitary (k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    lowGram k (Y * U) = lowGram k Y := by
  have h : (Y * U).submatrix (Subtype.val : LowIdx n k → Fin n) id =
      Y.submatrix (Subtype.val : LowIdx n k → Fin n) id * U := by
    ext i j
    simp [Matrix.mul_apply]
  rw [lowGram, h, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U,
    show U * Uᴴ = 1 from Matrix.mem_unitaryGroup_iff.mp hU, Matrix.one_mul]
  rfl

theorem lowRows_eq_mul (k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y.submatrix (Subtype.val : LowIdx n k → Fin n) id =
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix Subtype.val id * Y := by
  rw [← Matrix.submatrix_id_id Y, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.one_mul]
  rfl

theorem lowSelector_mul_conjTranspose (k : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : LowIdx n k → Fin n) id *
      ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : LowIdx n k → Fin n) id)ᴴ = 1 := by
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.conjTranspose_one, Matrix.one_mul]
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem lowMinor_one (k : ℕ) : lowMinor k (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [lowMinor, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

theorem lowGram_one (k : ℕ) : lowGram k (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [lowGram, lowSelector_mul_conjTranspose, Matrix.det_one]

/-- The Gram determinant of the rows `i ≥ k` of an invertible matrix is positive. -/
theorem lowGram_pos (k : ℕ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    0 < lowGram k Y := by
  apply Matrix.PosDef.det_pos
  apply Matrix.PosDef.mul_conjTranspose_self
  intro v w hvw
  have hP : ∀ x : LowIdx n k → ℂ, x = (x ᵥ* ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix
      (Subtype.val : LowIdx n k → Fin n) id)) ᵥ*
        ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : LowIdx n k → Fin n) id)ᴴ := by
    intro x
    rw [Matrix.vecMul_vecMul, lowSelector_mul_conjTranspose, Matrix.vecMul_one]
  have h1 : Function.Injective Y.vecMul := Matrix.vecMul_injective_iff_isUnit.mpr hY
  change v ᵥ* Y.submatrix Subtype.val id = w ᵥ* Y.submatrix Subtype.val id at hvw
  rw [lowRows_eq_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hvw
  rw [hP v, hP w, h1 hvw]

theorem lowGram_re_pos (k : ℕ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    0 < (lowGram k Y).re :=
  (Complex.pos_iff.mp (lowGram_pos k hY)).1

theorem lowGram_eq_re (k : ℕ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    lowGram k Y = ((lowGram k Y).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(Complex.pos_iff.mp (lowGram_pos k hY)).2]

end Minors

/-! ## Characters of `ℂˣ` -/

section Characters

/-- The function `z ↦ (z/‖z‖)^μ ‖z‖^(2w)`, with the power of `‖z‖` written as an
exponential. -/
def unitChar (μ : ℤ) (w : ℂ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ μ * Complex.exp (2 * w * (Real.log ‖z‖ : ℂ))

theorem unitChar_add (μ μ' : ℤ) (w w' : ℂ) {z : ℂ} (hz : z ≠ 0) :
    unitChar (μ + μ') (w + w') z = unitChar μ w z * unitChar μ' w' z := by
  have hu : z / (‖z‖ : ℂ) ≠ 0 :=
    div_ne_zero hz (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  rw [unitChar, unitChar, unitChar, zpow_add₀ hu,
    show 2 * (w + w') * (Real.log ‖z‖ : ℂ) =
      2 * w * (Real.log ‖z‖ : ℂ) + 2 * w' * (Real.log ‖z‖ : ℂ) by ring, Complex.exp_add]
  ring

theorem unitChar_zero_zero (z : ℂ) : unitChar 0 0 z = 1 := by
  simp [unitChar]

theorem unitChar_sum {ι : Type*} (s : Finset ι) (μ : ι → ℤ) (w : ι → ℂ) {z : ℂ}
    (hz : z ≠ 0) :
    unitChar (∑ i ∈ s, μ i) (∑ i ∈ s, w i) z = ∏ i ∈ s, unitChar (μ i) (w i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitChar_zero_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, unitChar_add _ _ _ _ hz,
      ih]

/-- The function `z ↦ z^p conj(z)^q exp(σ log |z|²)`. -/
def polyChar (p q : ℕ) (σ : ℂ) (z : ℂ) : ℂ :=
  z ^ p * starRingEnd ℂ z ^ q * Complex.exp (σ * (Real.log (Complex.normSq z) : ℂ))

theorem polyChar_eq_unitChar (p q : ℕ) (σ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    polyChar p q σ z = unitChar ((p : ℤ) - q) (((p : ℂ) + q) / 2 + σ) z := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hu : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz hr
  have hL : Complex.exp (Real.log ‖z‖ : ℂ) = (‖z‖ : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz)]
  have hz' : z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) := by field_simp
  have hc : starRingEnd ℂ z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ))⁻¹ := by
    have h1 : z * starRingEnd ℂ z = (‖z‖ : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    field_simp
    calc starRingEnd ℂ z * z = z * starRingEnd ℂ z := mul_comm _ _
      _ = (‖z‖ : ℂ) ^ 2 := h1
  have hN : (Real.log (Complex.normSq z) : ℂ) = 2 * (Real.log ‖z‖ : ℂ) := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  rw [polyChar, unitChar, hN, zpow_sub₀ hu, zpow_natCast, zpow_natCast, hc]
  conv_lhs => rw [hz']
  rw [mul_pow, mul_pow, inv_pow,
    show 2 * (((p : ℂ) + q) / 2 + σ) * (Real.log ‖z‖ : ℂ) =
      (p : ℂ) * (Real.log ‖z‖ : ℂ) + (q : ℂ) * (Real.log ‖z‖ : ℂ) +
        σ * (2 * (Real.log ‖z‖ : ℂ)) by ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, hL]
  field_simp

theorem polyChar_mul (p q : ℕ) (σ : ℂ) {z z' : ℂ} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    polyChar p q σ (z * z') = polyChar p q σ z * polyChar p q σ z' := by
  have h1 : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have h2 : Complex.normSq z' ≠ 0 := (Complex.normSq_pos.mpr hz').ne'
  simp only [polyChar, mul_pow, map_mul, Real.log_mul h1 h2, Complex.ofReal_add, mul_add,
    Complex.exp_add]
  ring

theorem polyChar_prod (p q : ℕ) (σ : ℂ) {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, z i ≠ 0) :
    polyChar p q σ (∏ i ∈ s, z i) = ∏ i ∈ s, polyChar p q σ (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyChar]
  | insert a s ha ih =>
    have hs : ∏ i ∈ s, z i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hz i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      polyChar_mul _ _ _ (hz a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hz i (Finset.mem_insert_of_mem hi)]

/-- The differences `m 0, m 1 - m 0, m 2 - m 1, …`. -/
def tele {A : Type*} [AddCommGroup A] (m : ℕ → A) : ℕ → A
  | 0 => m 0
  | k + 1 => m (k + 1) - m k

theorem sum_range_tele {A : Type*} [AddCommGroup A] (m : ℕ → A) (i : ℕ) :
    ∑ k ∈ Finset.range (i + 1), tele m k = m i := by
  induction i with
  | zero => simp [tele]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, tele]
    abel

theorem sum_fin_le_tele {A : Type*} [AddCommGroup A] {n : ℕ} (m : ℕ → A) (i : Fin n) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ i), tele m (k : ℕ) = m i := by
  rw [← sum_range_tele m i]
  have h : (Finset.univ.filter (fun k : Fin n => k ≤ i)).map Fin.valEmbedding =
      Finset.range ((i : ℕ) + 1) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Nat.lt_succ_of_le hk
    · intro hx
      exact ⟨⟨x, by omega⟩, Fin.mk_le_of_le_val (Nat.le_of_lt_succ hx), rfl⟩
  rw [← h, Finset.sum_map]
  rfl

/-- The weight of the character at each position, `0` past the end. -/
def posWeight : List ComplexCharacterData → ℕ → ℤ
  | [], _ => 0
  | d :: _, 0 => d.weight
  | _ :: ds, p + 1 => posWeight ds p

/-- The exponent of the character at each position, `0` past the end. -/
def posExponent : List ComplexCharacterData → ℕ → ℂ
  | [], _ => 0
  | d :: _, 0 => d.exponent
  | _ :: ds, p + 1 => posExponent ds p

theorem complexPositionCharacter_eq (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ) :
    complexPositionCharacter ds i z = unitChar (posWeight ds i) (posExponent ds i) z := by
  induction ds generalizing i with
  | nil => simp [complexPositionCharacter, posWeight, posExponent, unitChar]
  | cons d ds ih =>
    cases i with
    | zero =>
      have hr : (‖(z : ℂ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero)
      simp only [complexPositionCharacter, posWeight, posExponent]
      rw [d.character_eq, unitChar, Complex.cpow_def_of_ne_zero hr,
        ← Complex.ofReal_log (norm_nonneg _)]
      congr 2
      ring
    | succ p => exact ih p

theorem principalSeriesCharacter_eq (n : ℕ) (ds : List ComplexCharacterData)
    (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) a =
      ∏ i : Fin n, unitChar (posWeight ds i)
        (posExponent ds i + (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) (a i) := by
  rw [principalSeriesCharacter]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hr : ((‖((a i : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := norm_ne_zero_iff.mpr (a i).ne_zero
    exact_mod_cast pow_ne_zero 2 this
  rw [complexPositionCharacter_eq, Complex.finrank_real_complex, Complex.cpow_def_of_ne_zero hr,
    ← Complex.ofReal_log (by positivity), Real.log_pow, unitChar, unitChar, mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Characters

/-! ## The function on matrices -/

section Function

variable {n : ℕ}

/-- `D^p conj(D)^q exp(σ log G)` for the bottom-right minor `D = lowMinor k Y` and the Gram
determinant `G = lowGram k Y`. -/
def minorFactor (k p q : ℕ) (σ : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  lowMinor k Y ^ p * starRingEnd ℂ (lowMinor k Y) ^ q *
    Complex.exp (σ * (Real.log (lowGram k Y).re : ℂ))

theorem minorFactor_mul_of_isUpperTriangular (k p q : ℕ) (σ : ℂ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hd : ∏ i : LowIdx n k, b i.1 i.1 ≠ 0) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    minorFactor k p q σ (b * Y) =
      polyChar p q σ (∏ i : LowIdx n k, b i.1 i.1) * minorFactor k p q σ Y := by
  have hn : Complex.normSq (∏ i : LowIdx n k, b i.1 i.1) ≠ 0 := (Complex.normSq_pos.mpr hd).ne'
  have hG : (lowGram k Y).re ≠ 0 := (lowGram_re_pos k hY).ne'
  have hre : (lowGram k (b * Y)).re =
      Complex.normSq (∏ i : LowIdx n k, b i.1 i.1) * (lowGram k Y).re := by
    rw [lowGram_mul_of_isUpperTriangular k hb, Complex.re_ofReal_mul]
  rw [minorFactor, minorFactor, polyChar, lowMinor_mul_of_isUpperTriangular k hb, hre,
    Real.log_mul hn hG, Complex.ofReal_add, mul_add, Complex.exp_add, map_mul]
  ring

/-- The weights `μ k = m k - m (k-1)` of the minors, from the weights `m i` of the characters. -/
def nzWeight (ds : List ComplexCharacterData) : ℕ → ℤ :=
  tele (posWeight ds)

/-- The full exponents `W i = t i + ((n-1)/2 - i)` at each position. -/
def nzFullExponent (n : ℕ) (ds : List ComplexCharacterData) (i : ℕ) : ℂ :=
  posExponent ds i + (((n : ℂ) - 1) / 2 - (i : ℂ))

/-- The exponents `w k = W k - W (k-1)` of the minors. -/
def nzExponent (n : ℕ) (ds : List ComplexCharacterData) : ℕ → ℂ :=
  tele (nzFullExponent n ds)

/-- The factor of the `k`-th bottom-right minor. -/
def nzFactor (n : ℕ) (ds : List ComplexCharacterData) (k : ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  minorFactor k (nzWeight ds k).toNat (-nzWeight ds k).toNat
    (nzExponent n ds k - (((nzWeight ds k).toNat : ℂ) + ((-nzWeight ds k).toNat : ℂ)) / 2) Y

/-- The function `Y ↦ ∏ₖ nzFactor n ds k Y` on matrices. -/
def nzFunction (n : ℕ) (ds : List ComplexCharacterData) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ k : Fin n, nzFactor n ds k Y

theorem nzFactor_mul_of_isUpperTriangular (ds : List ComplexCharacterData) (k : ℕ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) (hd : ∀ i, b i i ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    nzFactor n ds k (b * Y) =
      (∏ i : LowIdx n k, unitChar (nzWeight ds k) (nzExponent n ds k) (b i.1 i.1)) *
        nzFactor n ds k Y := by
  rw [nzFactor, nzFactor, minorFactor_mul_of_isUpperTriangular _ _ _ _ hb
      (Finset.prod_ne_zero_iff.mpr fun i _ => hd i.1) hY,
    polyChar_prod _ _ _ _ _ fun i _ => hd i.1]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [polyChar_eq_unitChar _ _ _ (hd i.1), Int.toNat_sub_toNat_neg]
  congr 1
  ring

theorem prod_lowIdx_prod_unitChar (m : ℕ → ℤ) (W : ℕ → ℂ) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) :
    ∏ k : Fin n, ∏ i : LowIdx n k, unitChar (tele m k) (tele W k) (z i.1) =
      ∏ i : Fin n, unitChar (m i) (W i) (z i) := by
  classical
  have h1 : ∀ k : Fin n, ∏ i : LowIdx n k, unitChar (tele m k) (tele W k) (z i.1) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => (k : ℕ) ≤ (i : ℕ)),
        unitChar (tele m k) (tele W k) (z i) := fun k =>
    (Finset.prod_subtype (Finset.univ.filter fun i : Fin n => (k : ℕ) ≤ (i : ℕ))
      (fun i => by simp) (fun i => unitChar (tele m k) (tele W k) (z i))).symm
  rw [Finset.prod_congr rfl fun k _ => h1 k,
    Finset.prod_comm' (t' := Finset.univ)
      (s' := fun i => Finset.univ.filter (fun k : Fin n => k ≤ i))
      (fun k i => by simp)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← unitChar_sum _ (fun k : Fin n => tele m k) (fun k : Fin n => tele W k) (hz i),
    sum_fin_le_tele, sum_fin_le_tele]

theorem nzFunction_mul_of_isUpperTriangular (ds : List ComplexCharacterData)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) (hd : ∀ i, b i i ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y) :
    nzFunction n ds (b * Y) =
      (∏ i : Fin n, unitChar (posWeight ds i) (nzFullExponent n ds i) (b i i)) *
        nzFunction n ds Y := by
  rw [nzFunction, nzFunction,
    Finset.prod_congr rfl fun (k : Fin n) _ =>
      nzFactor_mul_of_isUpperTriangular ds (k : ℕ) hb hd hY,
    Finset.prod_mul_distrib]
  congr 1
  exact prod_lowIdx_prod_unitChar (posWeight ds) (nzFullExponent n ds) (fun i => b i i) hd

end Function

/-! ## Smoothness on the invertible matrices -/

section Smooth

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) :
    ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℂ => Y a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff

theorem contDiff_conj_entry (a b : Fin n) :
    ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℂ => starRingEnd ℂ (Y a b) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_entry a b)

theorem contDiff_det_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ) (hM : ∀ i j, ContDiff ℝ ∞ fun Y => M Y i j) :
    ContDiff ℝ ∞ fun Y => (M Y).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

theorem contDiff_lowMinor (k : ℕ) :
    ContDiff ℝ ∞ (lowMinor k : Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  contDiff_det_of_entries (fun Y => Y.submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val)
    fun i j => contDiff_entry i.1 j.1

theorem contDiff_lowGram (k : ℕ) :
    ContDiff ℝ ∞ (lowGram k : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  refine contDiff_det_of_entries (fun Y => Y.submatrix (Subtype.val : LowIdx n k → Fin n) id *
    (Y.submatrix (Subtype.val : LowIdx n k → Fin n) id)ᴴ) fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  exact ContDiff.sum fun l _ => (contDiff_entry _ _).mul (contDiff_conj_entry _ _)

theorem contDiffOn_minorFactor (k p q : ℕ) (σ : ℂ) :
    ContDiffOn ℝ ∞ (minorFactor k p q σ : Matrix (Fin n) (Fin n) ℂ → ℂ) {Y | IsUnit Y} := by
  have hlog : ContDiffOn ℝ ∞
      (fun Y : Matrix (Fin n) (Fin n) ℂ => Real.log (lowGram k Y).re) {Y | IsUnit Y} :=
    (Complex.reCLM.contDiff.comp (contDiff_lowGram k)).contDiffOn.log
      fun Y hY => (lowGram_re_pos k hY).ne'
  have hexp : ContDiffOn ℝ ∞ (fun Y : Matrix (Fin n) (Fin n) ℂ =>
      Complex.exp (σ * (Real.log (lowGram k Y).re : ℂ))) {Y | IsUnit Y} :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog)).cexp
  exact (((contDiff_lowMinor k).pow p).mul
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_lowMinor k)).pow q)).contDiffOn.mul
      hexp

theorem contDiffOn_nzFunction (ds : List ComplexCharacterData) :
    ContDiffOn ℝ ∞ (nzFunction n ds) {Y | IsUnit Y} :=
  contDiffOn_prod fun _ _ => contDiffOn_minorFactor _ _ _ _

end Smooth

/-! ## `U(n)`-finiteness -/

section KFinite

variable {n : ℕ}

/-- The function `g ↦ h (g a b)` on `GL_n(ℂ)`. -/
def entryFn (h : ℂ →+* ℂ) (a b : Fin n) : Langlands.GeneralLinear n ℂ → ℂ :=
  fun g => h ((g : Matrix (Fin n) (Fin n) ℂ) a b)

theorem entryFn_mem (h : ℂ →+* ℂ) (a b : Fin n) :
    entryFn h a b ∈ kFiniteSubalgebra (unitaryCompact ℂ n) := by
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun l : Fin n => entryFn h a l)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine mem_kFiniteSubalgebra_of_le _
    (Submodule.span ℂ (Set.range fun l : Fin n => entryFn h a l)) fun k _ => ?_
  have e : Whittaker.rightTranslation ℂ _ k (entryFn h a b) =
      ∑ l : Fin n, h ((k : Matrix (Fin n) (Fin n) ℂ) l b) • entryFn h a l := by
    ext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entryFn]
    show h (((g * k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) = _
    rw [Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem minorFn_mem (h : ℂ →+* ℂ) (k : ℕ) :
    (fun g : Langlands.GeneralLinear n ℂ => h (lowMinor k (g : Matrix (Fin n) (Fin n) ℂ))) ∈
      kFiniteSubalgebra (unitaryCompact ℂ n) := by
  have e : (fun g : Langlands.GeneralLinear n ℂ => h (lowMinor k (g : Matrix (Fin n) (Fin n) ℂ))) =
      (Matrix.of fun i j : LowIdx n k => entryFn h i.1 j.1).det := by
    ext g
    have e1 := RingHom.map_det (Pi.evalRingHom (fun _ : Langlands.GeneralLinear n ℂ => ℂ) g)
      (Matrix.of fun i j : LowIdx n k => entryFn h i.1 j.1)
    have e2 := RingHom.map_det h
      ((g : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val)
    rw [lowMinor, e2]
    refine Eq.trans ?_ e1.symm
    rfl
  rw [e]
  exact det_mem_subalgebra _ _ fun i j => entryFn_mem h i.1 j.1

theorem expFn_mem (σ : ℂ) (k : ℕ) :
    (fun g : Langlands.GeneralLinear n ℂ => Complex.exp
      (σ * (Real.log (lowGram k (g : Matrix (Fin n) (Fin n) ℂ)).re : ℂ))) ∈
      kFiniteSubalgebra (unitaryCompact ℂ n) := by
  refine mem_kFiniteSubalgebra_of_invariant _ fun u hu => ?_
  ext g
  show Complex.exp (σ * (Real.log (lowGram k
    ((g * u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).re : ℂ)) = _
  rw [Units.val_mul, lowGram_mul_unitary k _ (U := (u : Matrix (Fin n) (Fin n) ℂ)) hu]

theorem nzFunction_mem (ds : List ComplexCharacterData) :
    (fun g : Langlands.GeneralLinear n ℂ => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)) ∈
      kFiniteSubalgebra (unitaryCompact ℂ n) := by
  have e : (fun g : Langlands.GeneralLinear n ℂ => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)) =
      ∏ k : Fin n, fun g : Langlands.GeneralLinear n ℂ =>
        nzFactor n ds k (g : Matrix (Fin n) (Fin n) ℂ) := by
    ext g
    simp only [nzFunction, Finset.prod_apply]
  rw [e]
  refine Subalgebra.prod_mem _ fun k _ => ?_
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ (minorFn_mem (RingHom.id ℂ) k) _)
    (Subalgebra.pow_mem _ (minorFn_mem (starRingEnd ℂ) k) _)) (expFn_mem _ k)

end KFinite

/-! ## The nonzero `U(n)`-finite vector -/

theorem complexStandardNontrivial : ComplexStandardNontrivialStatement := by
  intro n ds _
  let f : Langlands.GeneralLinear n ℂ → ℂ :=
    fun g => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)
  have hsmooth : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f :=
    contMDiff_of_contDiffOn (contDiffOn_nzFunction ds) fun g => rfl
  have heq : ∀ (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ),
      f ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * g) =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) a * f g := by
    intro a u g
    have hu : ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular ∧
        ∀ i, ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := u.2
    have hb : (Matrix.diagonal (fun i => (a i : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular :=
      (Matrix.blockTriangular_diagonal _).mul hu.1
    have hbd : ∀ i, (Matrix.diagonal (fun i => (a i : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) i i = a i := by
      intro i
      rw [Matrix.diagonal_mul, hu.2 i, mul_one]
    show nzFunction n ds (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) = _
    rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val,
      nzFunction_mul_of_isUpperTriangular ds hb (fun i => by rw [hbd]; exact (a i).ne_zero)
        (Units.isUnit g), principalSeriesCharacter_eq]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hbd]
    rfl
  have hmem : f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
    ⟨⟨hsmooth, heq⟩, nzFunction_mem ds⟩
  have hf1 : f 1 = 1 := by
    show nzFunction n ds ((1 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Units.val_one]
    simp [nzFunction, nzFactor, minorFactor, lowMinor_one, lowGram_one]
  refine ⟨⟨⟨f, hmem⟩, 0, fun h => ?_⟩⟩
  have h1 := congrFun (congrArg Subtype.val h) 1
  rw [show (⟨f, hmem⟩ : kFiniteFunctions (complexStandardModule n ds)
    (unitaryCompact ℂ n)).val 1 = 1 from hf1] at h1
  exact one_ne_zero h1

end Langlands.Archimedean
