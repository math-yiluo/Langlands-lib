import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The Siegel upper half space

`Matrix.IsSiegel Ω` for a complex square matrix: `Ω` is symmetric and its imaginary part is positive
definite; `Matrix.siegelUpperHalfSpace ι` is the set of such matrices. Basic facts: real symmetric
plus `i` times positive definite is Siegel, diagonal Siegel matrices, block sums, scaling; every
Siegel matrix is `Pᵀ (diagonal t) P` with `P` real invertible and `Im tᵢ > 0`
(`Matrix.IsSiegel.exists_eq_transpose_mul_diagonal_mul`), hence invertible, and `-Ω⁻¹` is Siegel.

For a real symplectic `s = [[A, B], [C, D]]` and `P = A - iB`, `Q = C - iD`: `P` is invertible,
`-(Q P⁻¹)` is symmetric (`Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup`) and Siegel
(`Matrix.IsSiegel.neg_mul_inv_of_symplectic`): it is the image of `i · 1` under `s`, for the action
of `Sp_{2n}(ℝ)` on the Siegel upper half space by fractional linear transformations.
-/

open Complex Matrix MeasureTheory
open scoped Real

noncomputable section

namespace Langlands

variable {ι κ : Type*}

/-- `Ω` is in the Siegel upper half space: symmetric with positive definite imaginary part. -/
def Matrix.IsSiegel (Ω : Matrix ι ι ℂ) : Prop := Ω.IsSymm ∧ (Ω.map Complex.im).PosDef

/-- A symmetric matrix with positive definite imaginary part is Siegel. -/
theorem Matrix.IsSiegel.mk {Ω : Matrix ι ι ℂ} (isSymm : Ω.IsSymm) (posDef : (Ω.map Complex.im).PosDef) :
    Matrix.IsSiegel Ω := ⟨isSymm, posDef⟩

/-- A Siegel matrix is symmetric. -/
theorem Matrix.IsSiegel.isSymm {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) : Ω.IsSymm := h.1

/-- The imaginary part of a Siegel matrix is positive definite. -/
theorem Matrix.IsSiegel.posDef {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) : (Ω.map Complex.im).PosDef := h.2

/-- The Siegel upper half space: the set of Siegel matrices. -/
def Matrix.siegelUpperHalfSpace (ι : Type*) : Set (Matrix ι ι ℂ) := {Ω | Matrix.IsSiegel Ω}

/-- Membership in the Siegel upper half space. -/
@[simp] theorem Matrix.mem_siegelUpperHalfSpace {Ω : Matrix ι ι ℂ} :
    Ω ∈ Matrix.siegelUpperHalfSpace ι ↔ Matrix.IsSiegel Ω := Iff.rfl

/-- The imaginary part of a symmetric complex matrix is a real symmetric matrix. -/
theorem Matrix.isHermitian_map_im_of_isSymm {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) :
    (Ω.map Complex.im).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, h.apply]

/-- A symmetric matrix whose imaginary part is positive on nonzero real vectors is Siegel. -/
theorem Matrix.IsSiegel.of_dotProduct_pos [Fintype ι] {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm)
    (hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x)) : Matrix.IsSiegel Ω :=
  ⟨h, PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_map_im_of_isSymm h)
    fun x hx => by simpa using hpos x hx⟩

/-- The imaginary part of a Siegel matrix is positive on nonzero real vectors. -/
theorem Matrix.IsSiegel.dotProduct_pos [Fintype ι] {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simpa using h.posDef.dotProduct_mulVec_pos hx

/-- `X + iY` with `X` real symmetric and `Y` positive definite is Siegel. -/
theorem Matrix.isSiegel_ofReal_add_I_smul {X Y : Matrix ι ι ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    Matrix.IsSiegel (X.map ofReal + I • Y.map ofReal) := by
  have hY' : Y.IsSymm := by
    ext i j
    simpa using hY.isHermitian.apply i j
  refine ⟨?_, ?_⟩
  · ext i j
    simp [hX.apply, hY'.apply]
  · convert hY
    ext i j
    simp

/-- A diagonal matrix is Siegel if and only if its entries have positive imaginary part. -/
theorem Matrix.isSiegel_diagonal_iff [DecidableEq ι] {τ : ι → ℂ} :
    Matrix.IsSiegel (diagonal τ) ↔ ∀ i, 0 < (τ i).im := by
  have : (diagonal τ).map Complex.im = diagonal fun i => (τ i).im := diagonal_map (by simp)
  refine ⟨fun h => ?_, fun h => ⟨isSymm_diagonal _, ?_⟩⟩
  · simpa [this] using h.posDef
  · simpa [this] using h

/-- `i · 1` is Siegel. -/
theorem Matrix.isSiegel_I_smul_one [DecidableEq ι] : Matrix.IsSiegel (I • (1 : Matrix ι ι ℂ)) := by
  rw [smul_one_eq_diagonal, Matrix.isSiegel_diagonal_iff]
  simp

/-- In size one, Siegel means positive imaginary part. -/
theorem Matrix.isSiegel_unique_iff [Unique ι] {Ω : Matrix ι ι ℂ} :
    Matrix.IsSiegel Ω ↔ 0 < (Ω default default).im := by
  classical
  have : Ω = diagonal fun _ => Ω default default := by
    ext i j
    obtain rfl := Subsingleton.elim i default
    obtain rfl := Subsingleton.elim j default
    simp
  rw [this, Matrix.isSiegel_diagonal_iff]
  simp

/-- Positive real multiples of Siegel matrices are Siegel. -/
theorem Matrix.IsSiegel.smul {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) {q : ℝ} (hq : 0 < q) :
    Matrix.IsSiegel ((q : ℂ) • Ω) := by
  refine ⟨h.isSymm.smul _, ?_⟩
  convert h.posDef.smul hq using 1
  ext i j
  simp

/-- Positive integer multiples of Siegel matrices are Siegel. -/
theorem Matrix.IsSiegel.natCast_smul {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) {q : ℕ} (hq : 0 < q) :
    Matrix.IsSiegel ((q : ℂ) • Ω) := by
  simpa using h.smul (q := q) (by exact_mod_cast hq)

/-- Principal submatrices of Siegel matrices are Siegel. -/
theorem Matrix.IsSiegel.submatrix {Ω : Matrix ι ι ℂ} (h : Matrix.IsSiegel Ω) {e : κ → ι}
    (he : Function.Injective e) : Matrix.IsSiegel (Ω.submatrix e e) :=
  ⟨h.isSymm.submatrix e, h.posDef.submatrix he⟩

/-- A block diagonal matrix is Siegel if and only if its blocks are. -/
theorem Matrix.isSiegel_fromBlocks_iff [Finite ι] [Finite κ] {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} :
    Matrix.IsSiegel (fromBlocks Ω₁ 0 0 Ω₂) ↔ Matrix.IsSiegel Ω₁ ∧ Matrix.IsSiegel Ω₂ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  refine ⟨fun h => ⟨h.submatrix Sum.inl_injective, h.submatrix Sum.inr_injective⟩,
    fun ⟨h₁, h₂⟩ => Matrix.IsSiegel.of_dotProduct_pos ?_ fun x hx => ?_⟩
  · exact IsSymm.fromBlocks h₁.isSymm (by simp) h₂.isSymm
  · have e : x ⬝ᵥ ((fromBlocks Ω₁ 0 0 Ω₂).map Complex.im *ᵥ x) =
        (x ∘ Sum.inl) ⬝ᵥ (Ω₁.map Complex.im *ᵥ (x ∘ Sum.inl)) +
        (x ∘ Sum.inr) ⬝ᵥ (Ω₂.map Complex.im *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, mulVec, Fintype.sum_sum_type]
    have n₁ := h₁.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have n₂ := h₂.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    simp only [star_trivial] at n₁ n₂
    rw [e]
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := fun hr => hx (by
        funext i
        rcases i with i | i
        · exact congrFun hl i
        · exact congrFun hr i)
      linarith [h₂.dotProduct_pos hr]
    · linarith [h₁.dotProduct_pos hl]



section Finite

variable [Fintype ι] [DecidableEq ι]

open scoped MatrixOrder in

/-- Every Siegel matrix is `Pᵀ (diagonal t) P` with `P` real invertible and `Im tᵢ > 0`
(simultaneous diagonalization of the real and imaginary parts). -/
theorem Matrix.IsSiegel.exists_eq_transpose_mul_diagonal_mul {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) :
    ∃ P : Matrix ι ι ℝ, P.det ≠ 0 ∧ ∃ t : ι → ℂ, (∀ i, 0 < (t i).im) ∧
      σ = (P.map ofReal)ᵀ * diagonal t * P.map ofReal := by
  obtain ⟨B, hB, hY⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    h.posDef.isStrictlyPositive
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hY
  have hB' : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB
  have hX : (σ.map Complex.re).IsHermitian := by
    ext i j
    simp [conjTranspose_apply, h.isSymm.apply]
  have hX' : (B⁻¹ᴴ * σ.map Complex.re * B⁻¹).IsHermitian := isHermitian_conjTranspose_mul_mul _ hX
  obtain ⟨U, l, hUU, hs⟩ : ∃ (U : Matrix ι ι ℝ) (l : ι → ℝ), U * Uᵀ = 1 ∧
      B⁻¹ᵀ * σ.map Complex.re * B⁻¹ = U * diagonal l * Uᵀ :=
    ⟨hX'.eigenvectorUnitary.1, hX'.eigenvalues, Unitary.coe_mul_star_self hX'.eigenvectorUnitary,
      hX'.spectral_theorem⟩
  refine ⟨Uᵀ * B, ?_, fun i => l i + I, fun i => by simp, ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (isUnit_det_of_right_inverse hUU).ne_zero hB'.ne_zero
  have e1 : σ.map Complex.re = (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) := by
    have : (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) =
        Bᵀ * (U * diagonal l * Uᵀ) * B := by
      simp [Matrix.mul_assoc]
    rw [this, ← hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul,
      nonsing_inv_mul _ hB', transpose_one, Matrix.one_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hB', Matrix.mul_one]
  have e2 : σ.map Complex.im = (Uᵀ * B)ᵀ * (Uᵀ * B) := by
    rw [hY, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU,
      Matrix.one_mul]
  generalize Uᵀ * B = P at e1 e2
  ext i j
  have e1' := congrFun (congrFun e1 i) j
  have e2' := congrFun (congrFun e2 i) j
  simp only [mul_apply, map_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e1' e2' ⊢
  apply Complex.ext <;> simp [e1', e2']

omit [DecidableEq ι] in

/-- The complexification of `P *ᵥ x`. -/
theorem Matrix.ofReal_mulVec_eq (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    (fun i => ((P *ᵥ x) i : ℂ)) = P.map ofReal *ᵥ fun i => (x i : ℂ) := by
  ext i
  simp [mulVec, dotProduct]

/-- The complexification of an invertible real matrix is invertible. -/
theorem Matrix.isUnit_det_map_ofReal {P : Matrix ι ι ℝ} (hP : P.det ≠ 0) :
    IsUnit (P.map ofReal).det := by
  have : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
  rw [this]
  simpa using hP

/-- The inverse of the complexification is the complexification of the inverse. -/
theorem Matrix.inv_map_ofReal {P : Matrix ι ι ℝ} (hP : P.det ≠ 0) :
    (P.map ofReal)⁻¹ = P⁻¹.map ofReal := by
  refine inv_eq_right_inv ?_
  change P.map ofRealHom * P⁻¹.map ofRealHom = 1
  rw [← Matrix.map_mul, mul_nonsing_inv _ hP.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Real congruence preserves the Siegel upper half space. -/
theorem Matrix.IsSiegel.transpose_mul_mul {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) {P : Matrix ι ι ℝ}
    (hP : P.det ≠ 0) : Matrix.IsSiegel ((P.map ofReal)ᵀ * σ * P.map ofReal) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isSymm.eq,
      Matrix.mul_assoc]
  · convert h.posDef.conjTranspose_mul_mul_same (B := P)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det P).2 hP.isUnit)) using 1
    ext i j
    simp [mul_apply]

/-- Siegel matrices are invertible. -/
theorem Matrix.IsSiegel.isUnit_det {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) : IsUnit σ.det := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  rw [det_mul, det_mul, det_transpose, det_diagonal]
  refine ((Matrix.isUnit_det_map_ofReal hP).mul (IsUnit.mk0 _ ?_)).mul (Matrix.isUnit_det_map_ofReal hP)
  exact Finset.prod_ne_zero_iff.2 fun i _ h0 => by simpa [h0] using ht i

/-- The inverse of an invertible diagonal matrix. -/
theorem Matrix.inv_diagonal_of_ne_zero {t : ι → ℂ} (ht : ∀ i, t i ≠ 0) :
    (diagonal t)⁻¹ = diagonal fun i => (t i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  exact funext fun i => mul_inv_cancel₀ (ht i)

/-- `σ ↦ -σ⁻¹` preserves the Siegel upper half space. -/
theorem Matrix.IsSiegel.neg_inv {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) : Matrix.IsSiegel (-σ⁻¹) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have h1 : Matrix.IsSiegel (diagonal fun i => -(t i)⁻¹) := Matrix.isSiegel_diagonal_iff.2 fun i => by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (ht i) (normSq_pos.2 (ht0 i))
  have h2 : (P⁻¹ᵀ).det ≠ 0 := by
    rw [det_transpose]
    exact (isUnit_nonsing_inv_det _ hP.isUnit).ne_zero
  convert h1.transpose_mul_mul h2 using 1
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_diagonal_of_ne_zero ht0,
    ← transpose_nonsing_inv, Matrix.inv_map_ofReal hP, transpose_map, transpose_transpose,
    ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in

/-- Real symmetric translations preserve the Siegel upper half space. -/
theorem Matrix.IsSiegel.add_map_ofReal {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) {C : Matrix ι ι ℝ}
    (hC : C.IsSymm) : Matrix.IsSiegel (σ + C.map ofReal) := by
  refine ⟨h.isSymm.add (hC.map _), ?_⟩
  convert h.posDef using 1
  ext i j
  simp


end Finite

open scoped ComplexOrder in
private theorem herm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (Aᵀ + I • Bᵀ) * (C - I • D) - (Cᵀ + I • Dᵀ) * (A - I • B) = (-(2 * I)) • (1 : Matrix l l ℂ) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  rw [← h1, ← h2, e3, e4]
  module

open scoped ComplexOrder in
private theorem symm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (A - I • B)ᵀ * (C - I • D) = (C - I • D)ᵀ * (A - I • B) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [← h1, ← h2, e3, e4]
  module


section Symplectic

open scoped ComplexOrder

/-- For `s = [[A, B], [C, D]]` symplectic, `P = A - iB` is invertible and `-(Q P⁻¹)` is symmetric,
where `Q = C - iD`. -/
theorem Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ),
    (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) →
    s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  intro l _ _ s P Q hP hQ hs
  have hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈
      Matrix.symplecticGroup l ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hs'
  set A := s.toBlocks₁₁.map Complex.ofRealHom
  set B := s.toBlocks₁₂.map Complex.ofRealHom
  set C := s.toBlocks₂₁.map Complex.ofRealHom
  set D := s.toBlocks₂₂.map Complex.ofRealHom
  have h1 : Aᵀ * C = Cᵀ * A := by
    simp only [A, C, ← transpose_map, ← Matrix.map_mul, r1]
  have h2 : Bᵀ * D = Dᵀ * B := by
    simp only [B, D, ← transpose_map, ← Matrix.map_mul, r2]
  have h3 : Aᵀ * D - Cᵀ * B = 1 := by
    simp only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]
    rw [← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]; simp
  have ePQ : P = A - I • B ∧ Q = C - I • D := by
    constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      toBlocks₂₂]
  obtain ⟨eP, eQ⟩ := ePQ
  have hPc : Pᴴ = Aᵀ + I • Bᵀ := by
    rw [eP]; ext a b; simp [A, B, conjTranspose_apply, transpose_apply]
  have hQc : Qᴴ = Cᵀ + I • Dᵀ := by
    rw [eQ]; ext a b; simp [C, D, conjTranspose_apply, transpose_apply]
  have hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ) := by
    rw [hPc, hQc, eP, eQ]; exact herm_identity A B C D h1 h2 h3
  have hS : Pᵀ * Q = Qᵀ * P := by
    rw [eP, eQ]; exact symm_identity A B C D h1 h2 h3
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv,
        star_zero, zero_dotProduct]
    rw [hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at key
    have h2I : (-(2 * I)) ≠ 0 := by simp [I_ne_zero]
    have : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 key).resolve_left h2I
    exact hv0 (dotProduct_star_self_eq_zero.1 this)
  refine ⟨hdet, ?_⟩
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit Pᵀ.det := by rwa [det_transpose]
  apply Matrix.IsSymm.neg
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_nonsing_inv]
  calc Pᵀ⁻¹ * Qᵀ = Pᵀ⁻¹ * (Qᵀ * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]
    _ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]


/-- For `s = [[A, B], [C, D]]` symplectic, `P = A - iB` and `Q = C - iD`, the point `-(Q P⁻¹)` is in
the Siegel upper half space. -/
theorem Matrix.IsSiegel.neg_mul_inv_of_symplectic (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (hdet : P.det ≠ 0) (hsym : (-(Q * P⁻¹)).IsSymm) :
    Matrix.IsSiegel (-(Q * P⁻¹)) := by
  refine ⟨hsym, ?_⟩
  set A : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) with hA
  set B : Matrix l l ℂ := fun a b => (s (.inl a) (.inr b) : ℂ) with hB
  set C : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) with hC
  set D : Matrix l l ℂ := fun a b => (s (.inr a) (.inr b) : ℂ) with hD
  have hPe : P = A - I • B := by ext a b; simp only [hP]; rfl
  have hQe : Q = C - I • D := by ext a b; simp only [hQ]; rfl
  have hsc : s.map (Complex.ofRealHom : ℝ →+* ℂ) = fromBlocks A B C D := by
    ext (a|a) (b|b) <;> rfl
  have hJ : (J l ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) = J l ℂ := by
    ext (a|a) (b|b) <;> simp [J, one_apply, apply_ite]
  have hc : (fromBlocks A B C D)ᵀ * J l ℂ * fromBlocks A B C D = J l ℂ := by
    have h1 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (SymplecticGroup.mem_iff'.mp hs)
    simp only [Matrix.map_mul, transpose_map, hJ, hsc] at h1
    exact h1
  rw [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  obtain ⟨h11, h12, h21, h22⟩ := hc
  simp at h11 h12 h21 h22
  have star_real : ∀ X : Matrix l l ℂ, (∀ a b, star (X a b) = X a b) → Xᴴ = Xᵀ := by
    intro X hX; ext a b; simp [conjTranspose_apply, hX]
  have hAs : Aᴴ = Aᵀ := star_real A (fun a b => by simp [A])
  have hBs : Bᴴ = Bᵀ := star_real B (fun a b => by simp [B])
  have hCs : Cᴴ = Cᵀ := star_real C (fun a b => by simp [C])
  have hDs : Dᴴ = Dᵀ := star_real D (fun a b => by simp [D])
  have key : Pᴴ * Q - Qᴴ * P = -(2 * I) • (1 : Matrix l l ℂ) := by
    rw [hPe, hQe]
    simp only [conjTranspose_sub, conjTranspose_smul, hAs, hBs, hCs, hDs, Complex.star_def, conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -h11 - h22 + I • h12 - I • h21
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := -(Q * P⁻¹) with hτ
  have hτP : τ * P = -Q := by rw [hτ, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsymm : ∀ a b, τ b a = τ a b := fun a b => by
    have := congrFun (congrFun hsym a) b
    simpa [transpose_apply] using this
  set M : Matrix l l ℝ := τ.map im with hM
  set Mc : Matrix l l ℂ := M.map (Complex.ofRealHom : ℝ →+* ℂ) with hMc
  have hdiff : τ - τᴴ = (2 * I) • Mc := by
    ext a b
    simp only [Matrix.sub_apply, conjTranspose_apply, hsymm a b, Matrix.smul_apply, smul_eq_mul, Mc, M, map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hQP : Pᴴ * τᴴ = -Qᴴ := by rw [← conjTranspose_mul, hτP, conjTranspose_neg]
  have h2 : Pᴴ * Mc * P = 1 := by
    have e : Pᴴ * (τ - τᴴ) * P = (2 * I) • (1 : Matrix l l ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hτP, hQP]
      rw [Matrix.mul_neg, Matrix.neg_mul]
      linear_combination (norm := (match_scalars <;> ring_nf)) -key
    rw [hdiff, Matrix.mul_smul, Matrix.smul_mul] at e
    exact smul_right_injective _ (by simp [I_ne_zero] : (2 * I) ≠ 0) e
  have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hu, conjTranspose_one]
  have e2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hu
  have hMcf : Mc = (P⁻¹)ᴴ * P⁻¹ := by
    calc Mc = ((P⁻¹)ᴴ * Pᴴ) * Mc * (P * P⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * Mc * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h2, Matrix.mul_one]
  have hinj : Function.Injective (P⁻¹).mulVec := by
    intro u v h
    have := congrArg P.mulVec h
    simpa [mulVec_mulVec, e2] using this
  have hpd : Mc.PosDef := hMcf ▸ PosDef.conjTranspose_mul_self _ hinj
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp [conjTranspose_apply, M, hsymm a b]
  · intro x hx
    set xc : l → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h; apply hx; ext i
      have := congrFun h i
      simpa [xc] using this
    have e : star xc ⬝ᵥ Mc *ᵥ xc = ((star x ⬝ᵥ M *ᵥ x : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Mc, xc, Complex.ofReal_sum, Complex.ofReal_mul]
    have := hpd.dotProduct_mulVec_pos hxc0
    rw [e] at this
    exact zero_lt_real.mp this

end Symplectic

end Langlands
