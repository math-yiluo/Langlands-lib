import Langlands.Representation.Unitary.UnitarizabilityContinuationStatement
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Hecke.CornerDetermination
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences

/-!
# Proof of continuation of unitarizability along a connected parameter set

This module proves `Langlands.UnitarizabilityContinuationStatement`.

The proof first reduces to finite-dimensional linear algebra. For a matrix
family `A g` (`g ∈ G`) acting irreducibly on `ℂⁿ`, a matrix `B` is called
invariant when `(A g)ᴴ * B = B * A g⁻¹` for every `g`. Every nonzero invariant
matrix is invertible and the invariant matrices form a line (Schur's lemma).
If the family depends continuously on a real parameter in a preconnected set,
each member has a nonzero invariant matrix and one member has a positive
definite one, then every member has a positive definite invariant matrix: the
set of such parameters is closed and its complement is closed in the parameter
set, by compactness of the unit spheres.

For the representations, the matrices are the Hecke operators `P π_s(g) P` on
the finite-dimensional space of vectors fixed by a compact open subgroup
`K' ≤ K`, where `P` is the normalized-indicator projection onto these fixed
vectors. Since all members agree on `K`, these spaces and `P` do not depend on
the parameter. Restricting an invariant form of `π_s` to fixed vectors gives
an invariant matrix. Positivity on every fixed-vector space, normalized at one
fixed nonzero vector, gives an invariant positive form on the whole space.
-/

noncomputable section

namespace Langlands

universe uG uV

namespace UnitarizabilityContinuation

open Matrix Filter Topology

open scoped ComplexOrder

section MatrixFamily

variable {n : Type*} [Fintype n]
variable {G : Type*} [Group G]

/-- A matrix `B` is invariant for the family `A` when
`(A g)ᴴ * B = B * A g⁻¹` for every `g`. -/
def IsInvariantMatrix (A : G → Matrix n n ℂ) (B : Matrix n n ℂ) : Prop :=
  ∀ g, (A g)ᴴ * B = B * A g⁻¹

/-- The family `A` has no stable subspaces other than `⊥` and `⊤`. -/
def IsIrreducibleFamily (A : G → Matrix n n ℂ) : Prop :=
  ∀ U : Submodule ℂ (n → ℂ), (∀ g, ∀ x ∈ U, A g *ᵥ x ∈ U) → U = ⊥ ∨ U = ⊤

/-- The real part of the Hermitian expression `xᴴ H x`. -/
def quad (H : Matrix n n ℂ) (x : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (H *ᵥ x)).re

/-- A Hermitian matrix with `xᴴ H x > 0` for every nonzero `x`. -/
def IsPos (H : Matrix n n ℂ) : Prop :=
  H.IsHermitian ∧ ∀ x : n → ℂ, x ≠ 0 → 0 < quad H x

/-- The underlying function of a matrix, used for the sup norm. -/
def vec (H : Matrix n n ℂ) : n → n → ℂ :=
  Matrix.of.symm H

variable {A : G → Matrix n n ℂ}

theorem IsInvariantMatrix.add {B C : Matrix n n ℂ} (hB : IsInvariantMatrix A B)
    (hC : IsInvariantMatrix A C) : IsInvariantMatrix A (B + C) := by
  intro g
  rw [Matrix.mul_add, Matrix.add_mul, hB g, hC g]

theorem IsInvariantMatrix.smul (c : ℂ) {B : Matrix n n ℂ} (hB : IsInvariantMatrix A B) :
    IsInvariantMatrix A (c • B) := by
  intro g
  rw [Matrix.mul_smul, Matrix.smul_mul, hB g]

theorem IsInvariantMatrix.neg {B : Matrix n n ℂ} (hB : IsInvariantMatrix A B) :
    IsInvariantMatrix A (-B) := by
  intro g
  rw [Matrix.mul_neg, Matrix.neg_mul, hB g]

theorem IsInvariantMatrix.sub {B C : Matrix n n ℂ} (hB : IsInvariantMatrix A B)
    (hC : IsInvariantMatrix A C) : IsInvariantMatrix A (B - C) := by
  rw [sub_eq_add_neg]
  exact hB.add hC.neg

theorem IsInvariantMatrix.conjTranspose {B : Matrix n n ℂ} (hB : IsInvariantMatrix A B) :
    IsInvariantMatrix A Bᴴ := by
  intro g
  have h := congrArg Matrix.conjTranspose (hB g⁻¹)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    inv_inv] at h
  exact h.symm

/-- A nonzero invariant matrix has trivial kernel. -/
theorem eq_zero_of_mulVec_eq_zero [DecidableEq n] (hirr : IsIrreducibleFamily A) {B : Matrix n n ℂ}
    (hB : IsInvariantMatrix A B) (hB0 : B ≠ 0) {x : n → ℂ} (hx : B *ᵥ x = 0) : x = 0 := by
  let U : Submodule ℂ (n → ℂ) := LinearMap.ker (Matrix.mulVecLin B)
  have hU : ∀ g, ∀ y ∈ U, A g *ᵥ y ∈ U := by
    intro g y hy
    simp only [U, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
    have h := hB g⁻¹
    rw [inv_inv] at h
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
  rcases hirr U hU with h | h
  · have hxU : x ∈ U := by simpa [U] using hx
    rw [h] at hxU
    simpa using hxU
  · exfalso
    apply hB0
    apply Matrix.ext_of_mulVec_single
    intro i
    have hi : Pi.single i (1 : ℂ) ∈ U := h ▸ Submodule.mem_top
    simp only [U, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hi
    rw [hi, Matrix.zero_mulVec]

/-- Schur's lemma for invariant matrices: they form at most a line. -/
theorem exists_eq_smul_of_invariant [DecidableEq n] [Nonempty n] (hirr : IsIrreducibleFamily A)
    {H B : Matrix n n ℂ} (hH : IsInvariantMatrix A H) (hH0 : H ≠ 0)
    (hB : IsInvariantMatrix A B) : ∃ c : ℂ, B = c • H := by
  have hdet : IsUnit H.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv (eq_zero_of_mulVec_eq_zero hirr hH hH0 hHv)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (H⁻¹ * B))
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx' : (H⁻¹ * B) *ᵥ x = c • x := by
    simpa [Matrix.toLin'_apply] using hx.apply_eq_smul
  have hBx : (B - c • H) *ᵥ x = 0 := by
    have hB' : B *ᵥ x = H *ᵥ (c • x) := by
      rw [← hx', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    rw [Matrix.sub_mulVec, hB', Matrix.smul_mulVec, Matrix.mulVec_smul, sub_self]
  refine ⟨c, ?_⟩
  by_contra hne
  exact hx.2 (eq_zero_of_mulVec_eq_zero hirr (hB.sub (hH.smul c)) (sub_ne_zero.mpr hne) hBx)

/-- A nonzero invariant matrix yields a nonzero Hermitian invariant matrix. -/
theorem exists_hermitian_invariant {B : Matrix n n ℂ} (hB : IsInvariantMatrix A B)
    (hB0 : B ≠ 0) : ∃ H : Matrix n n ℂ, H.IsHermitian ∧ H ≠ 0 ∧ IsInvariantMatrix A H := by
  by_cases h : B + Bᴴ = 0
  · refine ⟨Complex.I • B, ?_, ?_, hB.smul _⟩
    · have hBh : Bᴴ = -B := eq_neg_of_add_eq_zero_right h
      change (Complex.I • B)ᴴ = Complex.I • B
      rw [Matrix.conjTranspose_smul, hBh, Complex.star_def, Complex.conj_I, smul_neg, neg_smul,
        neg_neg]
    · rw [Ne, smul_eq_zero, not_or]
      exact ⟨Complex.I_ne_zero, hB0⟩
  · refine ⟨B + Bᴴ, ?_, h, hB.add hB.conjTranspose⟩
    change (B + Bᴴ)ᴴ = B + Bᴴ
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

theorem quad_zero_right (H : Matrix n n ℂ) : quad H 0 = 0 := by
  simp [quad]

theorem quad_smul_real (r : ℝ) (H : Matrix n n ℂ) (x : n → ℂ) :
    quad ((r : ℂ) • H) x = r * quad H x := by
  simp [quad, Matrix.smul_mulVec, dotProduct_smul]

theorem quad_neg (H : Matrix n n ℂ) (x : n → ℂ) : quad (-H) x = -quad H x := by
  simp [quad, Matrix.neg_mulVec, dotProduct_neg]

theorem quad_smul_vec (r : ℝ) (H : Matrix n n ℂ) (x : n → ℂ) :
    quad H ((r : ℂ) • x) = r ^ 2 * quad H x := by
  simp [quad, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul]
  ring

theorem continuous_quad :
    Continuous (fun p : Matrix n n ℂ × (n → ℂ) => quad p.1 p.2) := by
  unfold quad
  exact Complex.continuous_re.comp
    ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd))

theorem IsPos.ne_zero [Nonempty n] {H : Matrix n n ℂ} (hH : IsPos H) : H ≠ 0 := by
  intro h0
  have hx : (fun _ : n => (1 : ℂ)) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary n)
    simp at this
  have := hH.2 _ hx
  rw [h0] at this
  simp [quad] at this

theorem IsPos.smul_real {H : Matrix n n ℂ} (hH : IsPos H) {r : ℝ} (hr : 0 < r) :
    IsPos ((r : ℂ) • H) := by
  refine ⟨?_, fun x hx => ?_⟩
  · change ((r : ℂ) • H)ᴴ = (r : ℂ) • H
    rw [Matrix.conjTranspose_smul, hH.1.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [quad_smul_real]
    exact mul_pos hr (hH.2 x hx)

omit [Fintype n] in
theorem isHermitian_real_smul {H : Matrix n n ℂ} (hH : H.IsHermitian) (r : ℝ) :
    ((r : ℂ) • H).IsHermitian := by
  change ((r : ℂ) • H)ᴴ = (r : ℂ) • H
  rw [Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

/-- A positive semidefinite nonzero invariant matrix is positive definite. -/
theorem isPos_of_nonneg [DecidableEq n] (hirr : IsIrreducibleFamily A) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hinv : IsInvariantMatrix A H) (h0 : H ≠ 0)
    (hnn : ∀ x, 0 ≤ quad H x) : IsPos H := by
  refine ⟨hH, fun x hx => lt_of_le_of_ne (hnn x) (fun hq => hx ?_)⟩
  have hpsd : H.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => by
    rw [Complex.nonneg_iff]
    refine ⟨hnn y, ?_⟩
    have := hH.im_star_dotProduct_mulVec_self y
    simp only [RCLike.im_to_complex] at this
    exact this.symm
  have hz : star x ⬝ᵥ H *ᵥ x = 0 := by
    apply Complex.ext
    · simpa [quad] using hq.symm
    · have := hH.im_star_dotProduct_mulVec_self x
      simpa only [RCLike.im_to_complex, Complex.zero_im] using this
  exact eq_zero_of_mulVec_eq_zero hirr hinv h0 ((hpsd.dotProduct_mulVec_zero_iff).mp hz)

omit [Fintype n] in
theorem vec_ne_zero {H : Matrix n n ℂ} (hH : H ≠ 0) : vec H ≠ 0 :=
  fun h => hH (Matrix.ext fun i j => congrFun (congrFun h i) j)

/-- A nonzero vector of a complex normed space has a positive real multiple of
norm one. -/
theorem exists_pos_real_smul_norm_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} (hx : x ≠ 0) : ∃ r : ℝ, 0 < r ∧ ‖(r : ℂ) • x‖ = 1 := by
  refine ⟨‖x‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr hx), ?_⟩
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Invariance passes to limits along convergent parameters in `J`. -/
theorem isInvariantMatrix_of_tendsto {A : ℝ → G → Matrix n n ℂ} {J : Set ℝ}
    (hcont : ∀ g, ContinuousOn (fun s => A s g) J) {t : ℝ} (ht : t ∈ J)
    {τ : ℕ → ℝ} (hτJ : ∀ k, τ k ∈ J) (hτ : Tendsto τ atTop (𝓝 t))
    {H : ℕ → Matrix n n ℂ} {H' : Matrix n n ℂ} (hH : Tendsto H atTop (𝓝 H'))
    (hinv : ∀ k, IsInvariantMatrix (A (τ k)) (H k)) : IsInvariantMatrix (A t) H' := by
  have hτ' : Tendsto τ atTop (𝓝[J] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτ, Eventually.of_forall hτJ⟩
  intro g
  have h1 : Tendsto (fun k => A (τ k) g) atTop (𝓝 (A t g)) :=
    ((hcont g) t ht).tendsto.comp hτ'
  have h2 : Tendsto (fun k => A (τ k) g⁻¹) atTop (𝓝 (A t g⁻¹)) :=
    ((hcont g⁻¹) t ht).tendsto.comp hτ'
  have hl : Tendsto (fun k => (A (τ k) g)ᴴ * H k) atTop (𝓝 ((A t g)ᴴ * H')) :=
    (h1.star).mul hH
  have hr : Tendsto (fun k => H k * A (τ k) g⁻¹) atTop (𝓝 (H' * A t g⁻¹)) :=
    hH.mul h2
  have hfun : (fun k => (A (τ k) g)ᴴ * H k) = fun k => H k * A (τ k) g⁻¹ :=
    funext fun k => hinv k g
  rw [hfun] at hl
  exact tendsto_nhds_unique hl hr

omit [Fintype n] in
theorem isHermitian_of_tendsto {H : ℕ → Matrix n n ℂ} {H' : Matrix n n ℂ}
    (hH : Tendsto H atTop (𝓝 H')) (hh : ∀ k, (H k).IsHermitian) : H'.IsHermitian := by
  have h1 : Tendsto (fun k => (H k)ᴴ) atTop (𝓝 H'ᴴ) :=
    hH.star
  have hfun : (fun k => (H k)ᴴ) = H := funext fun k => (hh k).eq
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 hH

theorem tendsto_quad {H : ℕ → Matrix n n ℂ} {H' : Matrix n n ℂ} {x : ℕ → n → ℂ}
    {x' : n → ℂ} (hH : Tendsto H atTop (𝓝 H')) (hx : Tendsto x atTop (𝓝 x')) :
    Tendsto (fun k => quad (H k) (x k)) atTop (𝓝 (quad H' x')) := by
  have hc : Tendsto (fun p : Matrix n n ℂ × (n → ℂ) => quad p.1 p.2) (𝓝 (H', x'))
      (𝓝 (quad H' x')) := continuous_quad.continuousAt.tendsto
  have hp : Tendsto (fun k => (H k, x k)) atTop (𝓝 (H', x')) := hH.prodMk_nhds hx
  have h := hc.comp hp
  rw [Function.comp_def] at h
  exact h

/-- Limits of positive definite invariant matrices: the parameters with a
positive definite invariant matrix are relatively closed in `J`. -/
theorem mem_of_mem_closure [DecidableEq n] [Nonempty n] {A : ℝ → G → Matrix n n ℂ} {J : Set ℝ}
    (hirr : ∀ s ∈ J, IsIrreducibleFamily (A s))
    (hcont : ∀ g, ContinuousOn (fun s => A s g) J) {t : ℝ} (ht : t ∈ J)
    (htD : t ∈ closure {s | s ∈ J ∧ ∃ H, IsPos H ∧ IsInvariantMatrix (A s) H}) :
    ∃ H, IsPos H ∧ IsInvariantMatrix (A t) H := by
  obtain ⟨τ, hτD, hτ⟩ := mem_closure_iff_seq_limit.mp htD
  choose hτJ H hHpos hHinv using hτD
  have hnorm : ∀ k, ∃ r : ℝ, 0 < r ∧ ‖(r : ℂ) • vec (H k)‖ = 1 := fun k =>
    exists_pos_real_smul_norm_eq_one (vec_ne_zero (hHpos k).ne_zero)
  choose r hr hr1 using hnorm
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_sphere (0 : n → n → ℂ) 1).tendsto_subseq
    (x := fun k => (r k : ℂ) • vec (H k)) (fun k => mem_sphere_zero_iff_norm.mpr (hr1 k))
  let H' : Matrix n n ℂ := Matrix.of a
  have hlim' : Tendsto (fun k => (r (φ k) : ℂ) • H (φ k)) atTop (𝓝 H') := hlim
  have hpos : ∀ k, IsPos ((r (φ k) : ℂ) • H (φ k)) := fun k =>
    (hHpos (φ k)).smul_real (hr (φ k))
  have hinv' : IsInvariantMatrix (A t) H' :=
    isInvariantMatrix_of_tendsto hcont ht (fun k => hτJ (φ k)) (hτ.comp hφ.tendsto_atTop)
      hlim' (fun k => (hHinv (φ k)).smul _)
  have hherm : H'.IsHermitian := isHermitian_of_tendsto hlim' (fun k => (hpos k).1)
  have hne : H' ≠ 0 := by
    intro h0
    have ha1 : ‖a‖ = 1 := mem_sphere_zero_iff_norm.mp ha
    have ha0 : a = 0 := funext fun i => funext fun j => congrFun (congrFun h0 i) j
    rw [ha0, norm_zero] at ha1
    exact zero_ne_one ha1
  have hnn : ∀ x, 0 ≤ quad H' x := by
    intro x
    refine ge_of_tendsto (tendsto_quad hlim' (tendsto_const_nhds (x := x)))
      (Eventually.of_forall fun k => ?_)
    by_cases hx : x = 0
    · rw [hx, quad_zero_right]
    · exact ((hpos k).2 x hx).le
  exact ⟨H', isPos_of_nonneg (hirr t ht) hherm hinv' hne hnn, hinv'⟩

/-- A parameter with a positive definite invariant matrix is not a limit of
parameters without one. -/
theorem not_mem_closure_compl [DecidableEq n] [Nonempty n] {A : ℝ → G → Matrix n n ℂ}
    {J : Set ℝ} (hirr : ∀ s ∈ J, IsIrreducibleFamily (A s))
    (hex : ∀ s ∈ J, ∃ B : Matrix n n ℂ, B ≠ 0 ∧ IsInvariantMatrix (A s) B)
    (hcont : ∀ g, ContinuousOn (fun s => A s g) J) {t : ℝ} (ht : t ∈ J)
    {H0 : Matrix n n ℂ} (hH0pos : IsPos H0) (hH0inv : IsInvariantMatrix (A t) H0) :
    t ∉ closure (J \ {s | s ∈ J ∧ ∃ H, IsPos H ∧ IsInvariantMatrix (A s) H}) := by
  intro htE
  obtain ⟨τ, hτE, hτ⟩ := mem_closure_iff_seq_limit.mp htE
  have hτJ : ∀ k, τ k ∈ J := fun k => (hτE k).1
  have hdata : ∀ k, ∃ H : Matrix n n ℂ, ∃ x y : n → ℂ, IsInvariantMatrix (A (τ k)) H ∧
      H.IsHermitian ∧ ‖vec H‖ = 1 ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ quad H x < 0 ∧ 0 < quad H y := by
    intro k
    obtain ⟨B, hB0, hBinv⟩ := hex (τ k) (hτJ k)
    obtain ⟨H, hHh, hH0, hHinv⟩ := exists_hermitian_invariant hBinv hB0
    have hnotD := (hτE k).2
    have hneg : ∃ x, quad H x < 0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hnotD ⟨hτJ k, H, isPos_of_nonneg (hirr _ (hτJ k)) hHh hHinv hH0 hcon, hHinv⟩
    have hpos : ∃ y, 0 < quad H y := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      refine hnotD ⟨hτJ k, -H, isPos_of_nonneg (hirr _ (hτJ k)) hHh.neg hHinv.neg
        (neg_ne_zero.mpr hH0) (fun y => ?_), hHinv.neg⟩
      rw [quad_neg]
      linarith [hcon y]
    obtain ⟨x, hx⟩ := hneg
    obtain ⟨y, hy⟩ := hpos
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [quad_zero_right] at hx
      exact lt_irrefl _ hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [quad_zero_right] at hy
      exact lt_irrefl _ hy
    obtain ⟨r, hr, hr1⟩ := exists_pos_real_smul_norm_eq_one (vec_ne_zero hH0)
    obtain ⟨a, ha, ha1⟩ := exists_pos_real_smul_norm_eq_one hx0
    obtain ⟨b, hb, hb1⟩ := exists_pos_real_smul_norm_eq_one hy0
    refine ⟨(r : ℂ) • H, (a : ℂ) • x, (b : ℂ) • y, hHinv.smul _, isHermitian_real_smul hHh r,
      hr1, ha1, hb1, ?_, ?_⟩
    · rw [quad_smul_real, quad_smul_vec]
      exact mul_neg_of_pos_of_neg hr (mul_neg_of_pos_of_neg (pow_pos ha 2) hx)
    · rw [quad_smul_real, quad_smul_vec]
      exact mul_pos hr (mul_pos (pow_pos hb 2) hy)
  choose H x y hHinv hHh hH1 hx1 hy1 hxneg hypos using hdata
  have hS : IsCompact (Metric.sphere (0 : n → n → ℂ) 1 ×ˢ
      (Metric.sphere (0 : n → ℂ) 1 ×ˢ Metric.sphere (0 : n → ℂ) 1)) :=
    (isCompact_sphere _ _).prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  obtain ⟨⟨a, x', y'⟩, ⟨ha, hx', hy'⟩, φ, hφ, hlim⟩ := hS.tendsto_subseq
    (x := fun k => (vec (H k), x k, y k))
    (fun k => ⟨mem_sphere_zero_iff_norm.mpr (hH1 k), mem_sphere_zero_iff_norm.mpr (hx1 k),
      mem_sphere_zero_iff_norm.mpr (hy1 k)⟩)
  let H' : Matrix n n ℂ := Matrix.of a
  have hlimH : Tendsto (fun k => H (φ k)) atTop (𝓝 H') :=
    (continuous_fst.tendsto _).comp hlim
  have hlimx : Tendsto (fun k => x (φ k)) atTop (𝓝 x') :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hlimy : Tendsto (fun k => y (φ k)) atTop (𝓝 y') :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hinv' : IsInvariantMatrix (A t) H' :=
    isInvariantMatrix_of_tendsto hcont ht (fun k => hτJ (φ k)) (hτ.comp hφ.tendsto_atTop)
      hlimH (fun k => hHinv (φ k))
  have hherm : H'.IsHermitian := isHermitian_of_tendsto hlimH (fun k => hHh (φ k))
  have hqx : quad H' x' ≤ 0 := le_of_tendsto (tendsto_quad hlimH hlimx)
    (Eventually.of_forall fun k => (hxneg (φ k)).le)
  have hqy : 0 ≤ quad H' y' := ge_of_tendsto (tendsto_quad hlimH hlimy)
    (Eventually.of_forall fun k => (hypos (φ k)).le)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_invariant (hirr t ht) hH0inv hH0pos.ne_zero hinv'
  have hcreal : (c.re : ℂ) = c := by
    rw [← Complex.conj_eq_iff_re]
    have h1 : (c • H0)ᴴ = c • H0 := by
      rw [← hc]
      exact hherm.eq
    rw [Matrix.conjTranspose_smul, hH0pos.1.eq] at h1
    have h2 : (star c - c) • H0 = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hH0pos.ne_zero
  rw [← hcreal] at hc
  have hx'0 : x' ≠ 0 := by
    rintro rfl
    rw [mem_sphere_zero_iff_norm, norm_zero] at hx'
    exact zero_ne_one hx'
  have hy'0 : y' ≠ 0 := by
    rintro rfl
    rw [mem_sphere_zero_iff_norm, norm_zero] at hy'
    exact zero_ne_one hy'
  have hpx := hH0pos.2 x' hx'0
  have hpy := hH0pos.2 y' hy'0
  rw [hc, quad_smul_real] at hqx hqy
  have hc0 : c.re = 0 := by
    have h1 : c.re ≤ 0 := by
      by_contra h
      linarith [mul_pos (not_le.mp h) hpx]
    have h2 : 0 ≤ c.re := by
      by_contra h
      linarith [mul_neg_of_neg_of_pos (not_le.mp h) hpy]
    linarith
  have hH'0 : H' = 0 := by rw [hc, hc0, Complex.ofReal_zero, zero_smul]
  have ha1 : ‖a‖ = 1 := mem_sphere_zero_iff_norm.mp ha
  have ha0 : a = 0 := funext fun i => funext fun j => congrFun (congrFun hH'0 i) j
  rw [ha0, norm_zero] at ha1
  exact zero_ne_one ha1

/-- Continuation of positive definite invariant matrices along a preconnected
parameter set. -/
theorem exists_isPos_of_isPreconnected [DecidableEq n] [Nonempty n]
    {A : ℝ → G → Matrix n n ℂ} {J : Set ℝ} (hJ : IsPreconnected J)
    (hirr : ∀ s ∈ J, IsIrreducibleFamily (A s))
    (hex : ∀ s ∈ J, ∃ B : Matrix n n ℂ, B ≠ 0 ∧ IsInvariantMatrix (A s) B)
    (hcont : ∀ g, ContinuousOn (fun s => A s g) J)
    {s₀ : ℝ} (hs₀ : s₀ ∈ J) (h₀ : ∃ H, IsPos H ∧ IsInvariantMatrix (A s₀) H) :
    ∀ s ∈ J, ∃ H, IsPos H ∧ IsInvariantMatrix (A s) H := by
  set D : Set ℝ := {s | s ∈ J ∧ ∃ H, IsPos H ∧ IsInvariantMatrix (A s) H} with hD
  have hmeet : J ∩ (closure D ∩ closure (J \ D)) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ht htD htE
    obtain ⟨H0, hH0pos, hH0inv⟩ := mem_of_mem_closure hirr hcont ht htD
    exact not_mem_closure_compl hirr hex hcont ht hH0pos hH0inv htE
  have hcover : J ⊆ closure D ∪ closure (J \ D) := by
    intro s hs
    by_cases h : s ∈ D
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure ⟨hs, h⟩)
  intro s hs
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hJ _ _ isClosed_closure
      isClosed_closure hcover hmeet with h | h
  · exact mem_of_mem_closure hirr hcont hs (h hs)
  · obtain ⟨H0, hH0pos, hH0inv⟩ := h₀
    exact absurd (h hs₀) (not_mem_closure_compl hirr hex hcont hs₀ hH0pos hH0inv)

/-- Two matrices with the same sesquilinear form are equal. -/
theorem matrix_ext_form [DecidableEq n] {M N : Matrix n n ℂ}
    (h : ∀ x y : n → ℂ, star x ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, Pi.star_single, single_dotProduct] using this

end MatrixFamily

section Irreducible

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The carrier of an irreducible representation is nonzero. -/
theorem exists_ne_zero_of_isIrreducible {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) :
    ∃ v : V, v ≠ 0 := by
  by_contra hcon
  simp only [ne_eq, not_exists, not_not] at hcon
  have hbt : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    change v ∈ (⊥ : Submodule ℂ V) ↔ v ∈ (⊤ : Submodule ℂ V)
    rw [hcon v]
    simp
  exact bot_ne_top hbt

end Irreducible

section PositiveForm

variable {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- The sesquilinear map of an invariant positive form. -/
def positiveFormSesq (ip : InvariantPositiveForm ρ) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v w => ip.inner v w)
    (fun v v' w => ip.add_left v v' w)
    (fun c v w => by rw [ip.smul_left, smul_eq_mul])
    (fun v w w' => by
      rw [← ip.conj_inner_symm, ip.add_left, map_add, ip.conj_inner_symm, ip.conj_inner_symm])
    (fun c v w => by
      rw [← ip.conj_inner_symm, ip.smul_left, map_mul, ip.conj_inner_symm, Complex.conj_conj,
        RingHom.id_apply, smul_eq_mul])

@[simp]
theorem positiveFormSesq_apply (ip : InvariantPositiveForm ρ) (v w : V) :
    positiveFormSesq ip v w = ip.inner v w := rfl

theorem positiveFormSesq_invariant (ip : InvariantPositiveForm ρ) (g : G) (v w : V) :
    positiveFormSesq ip (ρ g v) (ρ g w) = positiveFormSesq ip v w :=
  ip.invariant g v w

/-- An invariant positive form is positive on nonzero vectors. -/
theorem positiveForm_re_pos (ip : InvariantPositiveForm ρ) {v : V} (hv : v ≠ 0) :
    0 < (ip.inner v v).re := by
  have h1 : 0 ≤ (ip.inner v v).re := ip.re_inner_nonneg v
  have h2 : (ip.inner v v).im = 0 := Complex.conj_eq_iff_im.mp (ip.conj_inner_symm v v)
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact hv (ip.definite v (Complex.ext h.symm h2))

end PositiveForm

section Gram

variable {G : Type*} [Group G] [TopologicalSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {L : OpenSubgroup G}
  {n : Type*} [Fintype n] (e : Module.Basis n ℂ (fixedVectors ρ L.toSubgroup))

/-- The Gram matrix of a sesquilinear form on the basis `e`. -/
def gram (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => b (e i) (e j)

theorem gram_form (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x y : n → ℂ) :
    b (e.equivFun.symm x : V) (e.equivFun.symm y : V) = star x ⬝ᵥ (gram e b *ᵥ y) := by
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, gram, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, Complex.star_def]
  ring

/-- The Gram matrix of a positive form is positive definite. -/
theorem gram_isPos {σ : Representation ℂ G V} (ip : InvariantPositiveForm σ) :
    IsPos (gram e (positiveFormSesq ip)) := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, gram, Matrix.of_apply, positiveFormSesq_apply]
    exact ip.conj_inner_symm _ _
  · have hv : (e.equivFun.symm x : V) ≠ 0 := by
      intro h0
      apply hx
      have h1 : e.equivFun.symm x = 0 := Subtype.ext h0
      have h2 := congrArg e.equivFun h1
      rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
    have h := positiveForm_re_pos ip hv
    rw [← positiveFormSesq_apply, gram_form] at h
    exact h

end Gram

section FixedSpace

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A linear functional invariant under `L` is unchanged by the projection onto
`L`-fixed vectors. -/
theorem dual_fixedProjection (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : OpenSubgroup G)
    (hL : IsCompact (L : Set G)) (f : V →ₗ[ℂ] ℂ) (hf : ∀ k ∈ L, ∀ v, f (ρ k v) = f v) (v : V) :
    f (Hecke.fixedProjection μ ρ hρ L hL v : V) = f v := by
  rw [Hecke.fixedProjection_apply, Hecke.heckeAction_apply, Hecke.integratedAction_dual]
  have h : ∀ g, (Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ L hL)) g * f (ρ g v) =
      (L : Set G).indicator (fun _ => (μ.real (L : Set G) : ℂ)⁻¹ * f v) g := by
    intro g
    have e1 : (Hecke.HeckeAlgebra.toTestFunction μ
        (Hecke.HeckeAlgebra.normalizedIndicator μ L hL)) g =
        Hecke.HeckeAlgebra.normalizedIndicator μ L hL g := rfl
    rw [e1, Hecke.HeckeAlgebra.normalizedIndicator_apply]
    by_cases hg : g ∈ (L : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hf g hg, mul_one]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall h), integral_indicator_const _ L.isOpen.measurableSet,
    Complex.real_smul,
    mul_inv_cancel_left₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ L hL)]

variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ} {L : OpenSubgroup G}
  {hL : IsCompact (L : Set G)}

/-- An invariant sesquilinear form of a representation agreeing with `ρ` on `L`
is unchanged by projecting its first argument, when the second is `L`-fixed. -/
theorem form_fixedProjection_left {σ : Representation ℂ G V} (hσ : ∀ k ∈ L, σ k = ρ k)
    {b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hb : ∀ g v w, b (σ g v) (σ g w) = b v w)
    (v : V) {w : V} (hw : w ∈ fixedVectors ρ L.toSubgroup) :
    b (Hecke.fixedProjection μ ρ hρ L hL v : V) w = b v w := by
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun x => starRingEnd ℂ (b x w)
      map_add' := fun x y => by rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := fun c x => by
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply,
          smul_eq_mul] }
  have hf : ∀ k ∈ L, ∀ x, f (ρ k x) = f x := by
    intro k hk x
    have hwk : ρ k w = w := hw ⟨k, hk⟩
    change starRingEnd ℂ (b (ρ k x) w) = starRingEnd ℂ (b x w)
    congr 1
    calc b (ρ k x) w = b (σ k x) (σ k w) := by rw [hσ k hk, hwk]
      _ = b x w := hb k x w
  have := dual_fixedProjection μ ρ hρ L hL f hf v
  have h2 := congrArg (starRingEnd ℂ) this
  simpa [f] using h2

/-- The same statement for the second argument. -/
theorem form_fixedProjection_right {σ : Representation ℂ G V} (hσ : ∀ k ∈ L, σ k = ρ k)
    {b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hb : ∀ g v w, b (σ g v) (σ g w) = b v w)
    (v : V) {w : V} (hw : w ∈ fixedVectors ρ L.toSubgroup) :
    b w (Hecke.fixedProjection μ ρ hρ L hL v : V) = b w v := by
  have hf : ∀ k ∈ L, ∀ x, b w (ρ k x) = b w x := by
    intro k hk x
    have hwk : ρ k w = w := hw ⟨k, hk⟩
    calc b w (ρ k x) = b (σ k w) (σ k x) := by rw [hσ k hk, hwk]
      _ = b w x := hb k w x
  exact dual_fixedProjection μ ρ hρ L hL (b w) hf v

/-- The matrix of `P σ(g) P` on `L`-fixed vectors in the basis `e`, where `P`
is the projection onto `L`-fixed vectors. -/
def fixedMatrix {n : Type*} [Fintype n] (hρ : IsSmooth ρ) (hL : IsCompact (L : Set G))
    (e : Module.Basis n ℂ (fixedVectors ρ L.toSubgroup)) (σ : Representation ℂ G V) (g : G) :
    Matrix n n ℂ :=
  Matrix.of fun i j => e.equivFun (Hecke.fixedProjection μ ρ hρ L hL (σ g (e j))) i

variable {n : Type*} [Fintype n] (e : Module.Basis n ℂ (fixedVectors ρ L.toSubgroup))

theorem fixedMatrix_mulVec (σ : Representation ℂ G V) (g : G) (x : n → ℂ) :
    e.equivFun (Hecke.fixedProjection μ ρ hρ L hL (σ g (e.equivFun.symm x : V))) =
      fixedMatrix μ hρ hL e σ g *ᵥ x := by
  funext i
  simp [fixedMatrix, Matrix.mulVec, dotProduct, map_sum, mul_comm]

theorem coe_fixedProjection_symm (σ : Representation ℂ G V) (g : G) (x : n → ℂ) :
    (Hecke.fixedProjection μ ρ hρ L hL (σ g (e.equivFun.symm x : V)) : V) =
      (e.equivFun.symm (fixedMatrix μ hρ hL e σ g *ᵥ x) : V) := by
  rw [← fixedMatrix_mulVec, LinearEquiv.symm_apply_apply]

/-- Gram matrices of invariant forms are invariant matrices of the family. -/
theorem gram_isInvariant [DecidableEq n] {σ : Representation ℂ G V} (hσ : ∀ k ∈ L, σ k = ρ k)
    {b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hb : ∀ g v w, b (σ g v) (σ g w) = b v w) :
    IsInvariantMatrix (fixedMatrix μ hρ hL e σ) (gram e b) := by
  intro g
  apply matrix_ext_form
  intro x y
  have hu : (e.equivFun.symm x : V) ∈ fixedVectors ρ L.toSubgroup := (e.equivFun.symm x).2
  have hw : (e.equivFun.symm y : V) ∈ fixedVectors ρ L.toSubgroup := (e.equivFun.symm y).2
  have hl : star x ⬝ᵥ (((fixedMatrix μ hρ hL e σ g)ᴴ * gram e b) *ᵥ y) =
      b (σ g (e.equivFun.symm x : V)) (e.equivFun.symm y : V) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← gram_form,
      ← coe_fixedProjection_symm, form_fixedProjection_left μ hσ hb _ hw]
  have hr : star x ⬝ᵥ ((gram e b * fixedMatrix μ hρ hL e σ g⁻¹) *ᵥ y) =
      b (σ g (e.equivFun.symm x : V)) (e.equivFun.symm y : V) := by
    rw [← Matrix.mulVec_mulVec, ← gram_form, ← coe_fixedProjection_symm,
      form_fixedProjection_right μ hσ hb _ hu, ← hb g]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hl, hr]

/-- The family of fixed-vector matrices of an irreducible representation is
irreducible. -/
theorem fixedMatrix_isIrreducible {σ : Representation ℂ G V} (hirr : σ.IsIrreducible) :
    IsIrreducibleFamily (fixedMatrix μ hρ hL e σ) := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let crd : G → V →ₗ[ℂ] (n → ℂ) := fun g =>
    e.equivFun.toLinearMap ∘ₗ (Hecke.fixedProjection μ ρ hρ L hL) ∘ₗ σ g
  let S : Submodule ℂ V := ⨅ g, U.comap (crd g)
  have hmemS : ∀ v, v ∈ S ↔ ∀ g, e.equivFun (Hecke.fixedProjection μ ρ hρ L hL (σ g v)) ∈ U := by
    intro v
    simp [S, Submodule.mem_iInf, crd]
  have hS : ∀ h, ∀ v ∈ S, σ h v ∈ S := by
    intro h v hv
    rw [hmemS] at hv ⊢
    intro g
    have := hv (g * h)
    rwa [map_mul, Module.End.mul_apply] at this
  have hu : (e.equivFun.symm x : V) ∈ S := by
    rw [hmemS]
    intro g
    rw [fixedMatrix_mulVec]
    exact hU g x hxU
  rcases Hecke.submodule_eq_bot_or_eq_top_of_isIrreducible hirr S hS with h | h
  · exfalso
    apply hx0
    rw [h] at hu
    have h1 : e.equivFun.symm x = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp hu)
    have h2 := congrArg e.equivFun h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  · rw [eq_top_iff]
    intro y _
    have hy : (e.equivFun.symm y : V) ∈ S := h ▸ Submodule.mem_top
    rw [hmemS] at hy
    have := hy 1
    rwa [map_one, Module.End.one_apply, Hecke.fixedProjection_fixed,
      LinearEquiv.apply_symm_apply] at this

variable (hρ hL) in
include μ hρ hL in
/-- The Gram matrix of a nonzero invariant form of an irreducible representation
on a nonzero fixed-vector space is nonzero. -/
theorem gram_ne_zero {σ : Representation ℂ G V} (hσ : ∀ k ∈ L, σ k = ρ k)
    (hirr : σ.IsIrreducible) {b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hb0 : b ≠ 0)
    (hb : ∀ g v w, b (σ g v) (σ g w) = b v w) {w0 : V}
    (hw0 : w0 ∈ fixedVectors ρ L.toSubgroup) (hw0' : w0 ≠ 0) : gram e b ≠ 0 := by
  intro hg
  obtain ⟨x, hx⟩ : ∃ x, b x w0 ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    let R : Submodule ℂ V := LinearMap.ker b.flip
    have hmemR : ∀ v, v ∈ R ↔ ∀ x, b x v = 0 := by
      intro v
      simp only [R, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
        LinearMap.zero_apply]
    have hR : ∀ g, ∀ v ∈ R, σ g v ∈ R := by
      intro g v hv
      rw [hmemR] at hv ⊢
      intro x
      calc b x (σ g v) = b (σ g (σ g⁻¹ x)) (σ g v) := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        _ = b (σ g⁻¹ x) v := hb g _ _
        _ = 0 := hv _
    rcases Hecke.submodule_eq_bot_or_eq_top_of_isIrreducible hirr R hR with h | h
    · apply hw0'
      have hw : w0 ∈ R := (hmemR w0).mpr hcon
      rw [h] at hw
      exact (Submodule.mem_bot ℂ).mp hw
    · apply hb0
      ext v w
      have hw : w ∈ R := h ▸ Submodule.mem_top
      exact (hmemR w).mp hw v
  apply hx
  rw [← form_fixedProjection_left (hρ := hρ) (hL := hL) μ hσ hb x hw0]
  have h1 : (Hecke.fixedProjection μ ρ hρ L hL x : V) =
      (e.equivFun.symm (e.equivFun (Hecke.fixedProjection μ ρ hρ L hL x)) : V) := by
    rw [LinearEquiv.symm_apply_apply]
  have h2 : w0 = (e.equivFun.symm (e.equivFun ⟨w0, hw0⟩) : V) := by
    rw [LinearEquiv.symm_apply_apply]
  rw [h1, h2, gram_form, hg, Matrix.zero_mulVec, dotProduct_zero]

end FixedSpace


section LocalScalar

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On the vectors fixed by a compact open subgroup `L ≤ K`, a nonzero invariant
form of a member of the family is a nonzero multiple of a positive definite
Hermitian form. -/
theorem exists_local_scalar {π : ℝ → Representation ℂ G V} {J : Set ℝ} (K : OpenSubgroup G)
    (hJ : IsPreconnected J) (hagree : ∀ s ∈ J, ∀ t ∈ J, ∀ k ∈ K, π s k = π t k)
    (hirr : ∀ s ∈ J, (π s).IsIrreducible)
    (hex : ∀ s ∈ J, ∃ b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, b ≠ 0 ∧
      ∀ (g : G) (v w : V), b (π s g v) (π s g w) = b v w)
    (hcont : ∀ (g : G) (v : V) (ℓ : Module.Dual ℂ V), ContinuousOn (fun s => ℓ (π s g v)) J)
    {s₀ : ℝ} (hs₀ : s₀ ∈ J) (ip : InvariantPositiveForm (π s₀)) (hsm : IsSmooth (π s₀))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK : L ≤ K)
    [Module.Finite ℂ (fixedVectors (π s₀) L.toSubgroup)]
    {s : ℝ} (hs : s ∈ J) {b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hb0 : b ≠ 0)
    (hb : ∀ (g : G) (v w : V), b (π s g v) (π s g w) = b v w)
    {w0 : V} (hw0 : w0 ∈ fixedVectors (π s₀) L.toSubgroup) (hw0' : w0 ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ u ∈ fixedVectors (π s₀) L.toSubgroup, ∀ v ∈ fixedVectors (π s₀) L.toSubgroup,
        starRingEnd ℂ (c * b v u) = c * b u v) ∧
      ∀ u ∈ fixedVectors (π s₀) L.toSubgroup, u ≠ 0 → 0 < (c * b u u).re := by
  classical
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let L₀ : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨(L : Set G), hL⟩, by
      simpa only [L.isOpen.interior_eq] using (show (L : Set G).Nonempty from ⟨1, L.one_mem⟩)⟩
  let μ : Measure G := Measure.haarMeasure L₀
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure L₀
  let e := Module.finBasis ℂ (fixedVectors (π s₀) L.toSubgroup)
  have hd : 0 < Module.finrank ℂ (fixedVectors (π s₀) L.toSubgroup) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨w0, hw0⟩, fun h => hw0' (congrArg Subtype.val h)⟩
  have : Nonempty (Fin (Module.finrank ℂ (fixedVectors (π s₀) L.toSubgroup))) := ⟨⟨0, hd⟩⟩
  have hσ : ∀ t ∈ J, ∀ k ∈ L, π t k = π s₀ k := fun t ht k hk =>
    hagree t ht s₀ hs₀ k (hLK hk)
  have hAirr : ∀ t ∈ J, IsIrreducibleFamily (fixedMatrix μ hsm hL e (π t)) :=
    fun t ht => fixedMatrix_isIrreducible μ e (hirr t ht)
  have hAex : ∀ t ∈ J, ∃ B, B ≠ 0 ∧ IsInvariantMatrix (fixedMatrix μ hsm hL e (π t)) B := by
    intro t ht
    obtain ⟨b', hb'0, hb'⟩ := hex t ht
    exact ⟨gram e b', gram_ne_zero μ hsm hL e (hσ t ht) (hirr t ht) hb'0 hb' hw0 hw0',
      gram_isInvariant μ e (hσ t ht) hb'⟩
  have hAcont : ∀ g, ContinuousOn (fun t => fixedMatrix μ hsm hL e (π t) g) J := by
    intro g
    refine continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ?_
    exact hcont g (e j : V) (LinearMap.proj i ∘ₗ e.equivFun.toLinearMap ∘ₗ
      Hecke.fixedProjection μ (π s₀) hsm L hL)
  have h₀ : ∃ H, IsPos H ∧ IsInvariantMatrix (fixedMatrix μ hsm hL e (π s₀)) H :=
    ⟨gram e (positiveFormSesq ip), gram_isPos e ip,
      gram_isInvariant μ e (fun _ _ => rfl) (positiveFormSesq_invariant ip)⟩
  obtain ⟨H, hHpos, hHinv⟩ := exists_isPos_of_isPreconnected hJ hAirr hAex hAcont hs₀ h₀ s hs
  obtain ⟨c, hc⟩ := exists_eq_smul_of_invariant (hAirr s hs) hHinv hHpos.ne_zero
    (gram_isInvariant μ e (hσ s hs) hb)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact gram_ne_zero μ hsm hL e (hσ s hs) (hirr s hs) hb0 hb hw0 hw0' hc
  have key : ∀ x y, c⁻¹ * b (e.equivFun.symm x : V) (e.equivFun.symm y : V) =
      star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [gram_form, hc, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      inv_mul_cancel_left₀ hc0]
  have hrep : ∀ u ∈ fixedVectors (π s₀) L.toSubgroup, ∃ x, u = (e.equivFun.symm x : V) :=
    fun u hu => ⟨e.equivFun ⟨u, hu⟩, by rw [LinearEquiv.symm_apply_apply]⟩
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨x, rfl⟩ := hrep u hu
    obtain ⟨y, rfl⟩ := hrep v hv
    rw [key, key]
    exact hHpos.1.star_dotProduct_mulVec_comm y x
  · intro u hu hu0
    obtain ⟨x, rfl⟩ := hrep u hu
    have hx : x ≠ 0 := by
      rintro rfl
      exact hu0 (by simp)
    rw [key]
    exact hHpos.2 x hx

end LocalScalar

/-- Normalizing by a value `β` that becomes real and positive after multiplying by `c`. -/
theorem inv_mul_eq_mul_ofReal {β c z : ℂ} (hr : starRingEnd ℂ (c * β) = c * β)
    (hpos : 0 < (c * β).re) : β⁻¹ * z = c * z * (((c * β).re)⁻¹ : ℝ) := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hpos
  have h1 : (((c * β).re : ℝ) : ℂ) = c * β := Complex.conj_eq_iff_re.mp hr
  rw [Complex.ofReal_inv, h1, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hc, one_mul, mul_comm]

end UnitarizabilityContinuation

open UnitarizabilityContinuation in
/-- Unitarizability continues along a preconnected parameter set
(`UnitarizabilityContinuationStatement`). -/
theorem unitarizabilityContinuation : UnitarizabilityContinuationStatement.{uG, uV} := by
  intro G _ _ _ V _ _ π J K hK hJ hagree hadm hirr hex hcont s₀ hs₀ hU s hs
  obtain ⟨ip⟩ := hU
  obtain ⟨b, hb0, hb⟩ := hex s hs
  have hsm : IsSmooth (π s₀) := (hadm s₀ hs₀).1
  obtain ⟨w0, hw0⟩ := exists_ne_zero_of_isIrreducible (hirr s₀ hs₀)
  have hloc : ∀ x y : V, ∃ c : ℂ, starRingEnd ℂ (c * b w0 w0) = c * b w0 w0 ∧
      0 < (c * b w0 w0).re ∧ starRingEnd ℂ (c * b y x) = c * b x y ∧
      (x ≠ 0 → 0 < (c * b x x).re) := by
    intro x y
    obtain ⟨H0, hH0⟩ := hsm w0
    obtain ⟨H1, hH1⟩ := hsm x
    obtain ⟨H2, hH2⟩ := hsm y
    have hLK : K ⊓ H0 ⊓ H1 ⊓ H2 ≤ K := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hL : IsCompact ((K ⊓ H0 ⊓ H1 ⊓ H2 : OpenSubgroup G) : Set G) :=
      hK.of_isClosed_subset (OpenSubgroup.isClosed _) fun g hg => hLK hg
    have hmem : ∀ {H : OpenSubgroup G}, K ⊓ H0 ⊓ H1 ⊓ H2 ≤ H → ∀ {v : V},
        v ∈ fixedVectors (π s₀) H.toSubgroup →
          v ∈ fixedVectors (π s₀) (K ⊓ H0 ⊓ H1 ⊓ H2).toSubgroup :=
      fun hLH v hv g => hv ⟨g.1, hLH g.2⟩
    have : Module.Finite ℂ (fixedVectors (π s₀) (K ⊓ H0 ⊓ H1 ⊓ H2).toSubgroup) :=
      (hadm s₀ hs₀).2 _
    have hw0L := hmem (inf_le_left.trans (inf_le_left.trans inf_le_right)) hH0
    have hxL := hmem (inf_le_left.trans inf_le_right) hH1
    have hyL := hmem inf_le_right hH2
    obtain ⟨c, -, hherm, hpos⟩ := exists_local_scalar K hJ hagree hirr hex hcont hs₀ ip hsm
      (K ⊓ H0 ⊓ H1 ⊓ H2) hL hLK hs hb0 hb hw0L hw0
    exact ⟨c, hherm w0 hw0L w0 hw0L, hpos w0 hw0L hw0, hherm x hxL y hyL,
      fun hx => hpos x hxL hx⟩
  have hsymm : ∀ x y : V, starRingEnd ℂ ((b w0 w0)⁻¹ * b y x) = (b w0 w0)⁻¹ * b x y := by
    intro x y
    obtain ⟨c, h1, h2, h3, -⟩ := hloc x y
    rw [inv_mul_eq_mul_ofReal h1 h2, inv_mul_eq_mul_ofReal h1 h2, map_mul, Complex.conj_ofReal,
      h3]
  have hpos : ∀ x : V, x ≠ 0 → 0 < ((b w0 w0)⁻¹ * b x x).re := by
    intro x hx
    obtain ⟨c, h1, h2, -, h4⟩ := hloc x x
    rw [inv_mul_eq_mul_ofReal h1 h2, Complex.re_mul_ofReal]
    exact mul_pos (h4 hx) (inv_pos.mpr h2)
  exact ⟨{ inner := fun x y => (b w0 w0)⁻¹ * b x y
           conj_inner_symm := fun x y => hsymm x y
           re_inner_nonneg := fun x => by
             rw [RCLike.re_to_complex]
             by_cases hx : x = 0
             · rw [hx, map_zero, mul_zero, Complex.zero_re]
             · exact (hpos x hx).le
           add_left := fun x y z => by
             change (b w0 w0)⁻¹ * b (x + y) z = (b w0 w0)⁻¹ * b x z + (b w0 w0)⁻¹ * b y z
             rw [map_add, LinearMap.add_apply, mul_add]
           smul_left := fun x y r => by
             change (b w0 w0)⁻¹ * b (r • x) y = starRingEnd ℂ r * ((b w0 w0)⁻¹ * b x y)
             rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, mul_left_comm]
           definite := fun x hx => by
             by_contra hx0
             have h := hpos x hx0
             change (b w0 w0)⁻¹ * b x x = 0 at hx
             rw [hx, Complex.zero_re] at h
             exact lt_irrefl _ h
           invariant := fun g v w => by
             rw [hb] }⟩

end Langlands
