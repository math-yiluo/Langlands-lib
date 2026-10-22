import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.RankMaps
import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# JPSS functions on the actual left-unipotent quotient

The scalar integrals expose the measure and integrability. No Haar normalization,
convergence, rational continuation, or local factor is selected by these definitions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The actual left coset space `N_(n+1) \ GL_(n+1)`, including rank one.
It is the published right-relation quotient `QuotientIntegration.LeftQuotient`. -/
abbrev LeftUnipotentQuotient (n : ℕ) (F : Type uF) [Field F] :=
  QuotientIntegration.LeftQuotient (upperUnipotent (n + 1) F)

/-- Standard-character equivariant functions on the actual general linear group.
Coefficient-model vectors have values in this space. -/
abbrev WhittakerFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :=
  (equivariantFunctions (upperUnipotent (n + 1) F)
    (standardCharacter ψ n)).toSubmodule

/-- The inverse-character space used for the second member of a JPSS pair. -/
abbrev InverseWhittakerFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :=
  (equivariantFunctions (upperUnipotent (n + 1) F)
    (inverseStandardCharacter ψ n)).toSubmodule

omit [TopologicalSpace F] in
/-- Upper-unipotent matrices have determinant one, over any field. -/
@[simp] theorem unipotent_det {n : ℕ} (u : upperUnipotent n F) :
    Matrix.det u.val.val = 1 := by
  rw [Matrix.det_of_isUpperTriangular u.property.1]
  simp only [UpperUnipotent.entry_diag, Finset.prod_const_one]

/-- The last row of a positive-rank invertible matrix. -/
def lastRow {n : ℕ} (g : Langlands.GeneralLinear (n + 1) F) : Fin (n + 1) → F :=
  fun j => g (Fin.last n) j

omit [TopologicalSpace F] in
/-- Left upper-unipotent multiplication fixes the last row. -/
@[simp] theorem lastRow_unipotent_mul {n : ℕ} (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    lastRow (u.val * g) = lastRow g := by
  funext j
  change ∑ i : Fin (n + 1), u.val (Fin.last n) i * g i j = g (Fin.last n) j
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro i _ hi
    have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
    rw [UpperUnipotent.entry_eq_zero u hil, zero_mul]
  · simp

/-- The actual spectral weight `|det g|^s`, with the absolute value explicit.
It uses the usual complex power of the positive real determinant norm. -/
def determinantWeight (abv : AbsoluteValue F ℝ) {n : ℕ}
    (g : Langlands.GeneralLinear n F) (s : ℂ) : ℂ :=
  (abv (Matrix.det g.val) : ℂ) ^ s

omit [TopologicalSpace F] in
@[simp] theorem determinantWeight_unipotent_mul (abv : AbsoluteValue F ℝ)
    {n : ℕ} (u : upperUnipotent n F) (g : Langlands.GeneralLinear n F) (s : ℂ) :
    determinantWeight abv (u.val * g) s = determinantWeight abv g s := by
  simp [determinantWeight, Matrix.det_mul]

/-- Cancellation of the standard and inverse characters under left translation. -/
theorem whittaker_product_invariant (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    W.val (u.val * g) * W'.val (u.val * g) = W.val g * W'.val g := by
  rw [W.property u g, W'.property u g]
  change ((standardCharacter ψ n u : ℂ) * W.val g) *
      ((((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * W'.val g) =
    W.val g * W'.val g
  rw [mul_mul_mul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- Equal-rank JPSS integrand on `GL_(n+1)` before descent to the quotient. -/
def equalRankFunction (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  W.val g * W'.val g * Φ (lastRow g) * determinantWeight abv g s

theorem equalRankFunction_invariant (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    equalRankFunction ψ abv W W' Φ s (u.val * g) =
      equalRankFunction ψ abv W W' Φ s g := by
  unfold equalRankFunction
  rw [whittaker_product_invariant, lastRow_unipotent_mul,
    determinantWeight_unipotent_mul]

/-- The representative-independent equal-rank integrand on the actual left quotient. -/
def equalRankIntegrand (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    LeftUnipotentQuotient n F → ℂ :=
  QuotientIntegration.descend _ (equalRankFunction ψ abv W W' Φ s)
    (equalRankFunction_invariant ψ abv W W' Φ s)

@[simp] theorem equalRankIntegrand_mk (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    equalRankIntegrand ψ abv W W' Φ s (Quotient.mk _ g) =
      W.val g * W'.val g * Φ (lastRow g) * determinantWeight abv g s := rfl

/-- Absolute convergence of the equal-rank scalar integral for the supplied quotient
measure. This predicate is separate from the total Bochner integral. -/
def EqualRankConverges (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) : Prop :=
  Integrable (equalRankIntegrand ψ abv W W' Φ s) μ

/-- The equal-rank JPSS scalar integral with its quotient measure supplied explicitly.
The name alone asserts neither convergence nor a normalized Haar measure. -/
def equalRankIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) : ℂ :=
  ∫ q, equalRankIntegrand ψ abv W W' Φ s q ∂μ

omit [TopologicalSpace F] in
/-- The corank-one block inclusion maps actual upper-unipotent matrices into
actual upper-unipotent matrices. -/
theorem corankOne_mem_unipotent {n : ℕ} (u : upperUnipotent (n + 1) F) :
    rankInclusion 1 u.val ∈ upperUnipotent ((n + 1) + 1) F := by
  constructor
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (lt_irrefl _ hij).elim
      | cast j =>
        change blockSum (u.val, 1) ((0 : Fin 1).natAdd (n + 1)) (j.castAdd 1) = 0
        exact blockSum_apply_right_left _ _ _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
      | cast j =>
        change blockSum (u.val, 1) (i.castAdd 1) (j.castAdd 1) = 0
        rw [blockSum_apply_left]
        exact UpperUnipotent.entry_eq_zero u hij
  · intro i
    induction i using Fin.lastCases with
    | last =>
      change blockSum (u.val, 1) ((0 : Fin 1).natAdd (n + 1))
        ((0 : Fin 1).natAdd (n + 1)) = 1
      simp
    | cast i =>
      change blockSum (u.val, 1) (i.castAdd 1) (i.castAdd 1) = 1
      simp

/-- The subgroup-valued corank-one inclusion, constructed from the shared rank map. -/
def corankOneUnipotent {n : ℕ} (u : upperUnipotent (n + 1) F) :
    upperUnipotent ((n + 1) + 1) F :=
  ⟨rankInclusion 1 u.val, corankOne_mem_unipotent u⟩

/-- The first-superdiagonal character is preserved by adjoining a final unit block. -/
@[simp] theorem corankOne_standardCharacter (ψ : UnitaryAdditiveCharacter F)
    {n : ℕ} (u : upperUnipotent (n + 1) F) :
    standardCharacter ψ (n + 1) (corankOneUnipotent u) =
      standardCharacter ψ n u := by
  apply Units.ext
  simp only [standardCharacter_apply]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hlast : (corankOneUnipotent u).val (Fin.last n).castSucc (Fin.last n).succ = 0 := by
    change blockSum (u.val, 1) ((Fin.last n).castAdd 1)
      ((0 : Fin 1).natAdd (n + 1)) = 0
    exact blockSum_apply_left_right _ _ _ _
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  change blockSum (u.val, 1) (i.castSucc.castAdd 1) (i.succ.castAdd 1) = _
  exact blockSum_apply_left _ _ _ _

/-- Corank-one JPSS function on the smaller general linear group. -/
def corankOneFunction (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  W.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2)

theorem corankOneFunction_invariant (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    corankOneFunction ψ abv W W' s (u.val * g) =
      corankOneFunction ψ abv W W' s g := by
  unfold corankOneFunction
  rw [map_mul, determinantWeight_unipotent_mul]
  change W.val ((corankOneUnipotent u).val * rankInclusion 1 g) *
      W'.val (u.val * g) * _ = _
  rw [W.property, W'.property, corankOne_standardCharacter]
  change ((standardCharacter ψ n u : ℂ) * W.val (rankInclusion 1 g)) *
      ((((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * W'.val g) * _ = _
  rw [mul_mul_mul_comm (standardCharacter ψ n u : ℂ), ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

/-- The corank-one integrand descended to `N_(n+1) \ GL_(n+1)`. -/
def corankOneIntegrand (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) : LeftUnipotentQuotient n F → ℂ :=
  QuotientIntegration.descend _ (corankOneFunction ψ abv W W' s)
    (corankOneFunction_invariant ψ abv W W' s)

@[simp] theorem corankOneIntegrand_mk (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F) :
    corankOneIntegrand ψ abv W W' s (Quotient.mk _ g) =
      W.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2) := rfl

/-- Absolute convergence for the corank-one scalar integral and explicit measure. -/
def CorankOneConverges (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) : Prop :=
  Integrable (corankOneIntegrand ψ abv W W' s) μ

/-- The corank-one JPSS scalar integral, with measure and spectral variable explicit. -/
def corankOneIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) : ℂ :=
  ∫ q, corankOneIntegrand ψ abv W W' s q ∂μ

/-- Adjoin `d` final identity coordinates by iterating the shared corank-one map.
The source has rank `n + 1` and the target rank `n + d + 1`. -/
def appendIdentity (n : ℕ) : (d : ℕ) →
    Langlands.GeneralLinear (n + 1) F →* Langlands.GeneralLinear (n + d + 1) F
  | 0 => MonoidHom.id _
  | d + 1 => (rankInclusion 1).comp (appendIdentity n d)

omit [TopologicalSpace F] in
/-- Entrywise verification that the iterated map is exactly `diag(g,I_d)`. -/
theorem appendIdentity_entry (n d : ℕ) (g : Langlands.GeneralLinear (n + 1) F) :
    ∀ i j : Fin (n + d + 1),
      appendIdentity n d g i j =
        if hi : i.val < n + 1 then
          if hj : j.val < n + 1 then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
        else if i = j then 1 else 0 := by
  induction d with
  | zero =>
    intro i j
    simp [appendIdentity, i.isLt, j.isLt]
  | succ d ih =>
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        change blockSum (appendIdentity n d g, 1)
          ((0 : Fin 1).natAdd (n + d + 1)) ((0 : Fin 1).natAdd (n + d + 1)) = _
        simp
      | cast j =>
        change blockSum (appendIdentity n d g, 1)
          ((0 : Fin 1).natAdd (n + d + 1)) (j.castAdd 1) = _
        simp [ne_comm, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        change blockSum (appendIdentity n d g, 1) (i.castAdd 1)
          ((0 : Fin 1).natAdd (n + d + 1)) = _
        simp [Fin.castSucc_ne_last]
      | cast j =>
        change blockSum (appendIdentity n d g, 1) (i.castAdd 1) (j.castAdd 1) = _
        simpa using ih i j

/-- The corresponding actual inclusion of upper-unipotent groups. -/
def appendUnipotent {n : ℕ} (u : upperUnipotent (n + 1) F) :
    (d : ℕ) → upperUnipotent (n + d + 1) F
  | 0 => u
  | d + 1 => corankOneUnipotent (appendUnipotent u d)

omit [TopologicalSpace F] in
@[simp] theorem appendUnipotent_val {n : ℕ} (u : upperUnipotent (n + 1) F) (d : ℕ) :
    (appendUnipotent u d).val = appendIdentity n d u.val := by
  induction d with
  | zero => rfl
  | succ d ih => exact congrArg (rankInclusion 1) ih

@[simp] theorem appendUnipotent_character (ψ : UnitaryAdditiveCharacter F)
    {n : ℕ} (u : upperUnipotent (n + 1) F) (d : ℕ) :
    standardCharacter ψ (n + d) (appendUnipotent u d) =
      standardCharacter ψ n u := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change standardCharacter ψ ((n + d) + 1)
      (corankOneUnipotent (appendUnipotent u d)) = _
    rw [corankOne_standardCharacter, ih]

/-- The rectangular `x` block in the unequal-rank JPSS matrix, extended by zero.
Its rows are the `j` positions immediately below the leading rank `n + 1` block. -/
def rectangularEntries {n : ℕ} (j k : ℕ) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    Matrix (Fin (n + (j + k + 1) + 1)) (Fin (n + (j + k + 1) + 1)) F :=
  fun a b =>
    if ha : n + 1 ≤ a.val ∧ a.val < n + 1 + j then
      if hb : b.val < n + 1 then
        x ⟨a.val - (n + 1), by omega⟩ ⟨b.val, hb⟩
      else 0
    else 0

omit [TopologicalSpace F] in
/-- The rectangular off-diagonal block is square-zero. -/
theorem rectangularEntries_sq {n : ℕ} (j k : ℕ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    rectangularEntries j k x * rectangularEntries j k x = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c.val < n + 1
  · have hr : ¬ (n + 1 ≤ c.val ∧ c.val < n + 1 + j) := by omega
    simp only [rectangularEntries, dite_eq_right hr, mul_zero]
  · simp [rectangularEntries, hc]

/-- The actual invertible matrix `1 + X`, with inverse `1 - X`, for the
rectangular block in the JPSS integral. -/
def rectangularUnipotent {n : ℕ} (j k : ℕ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    Langlands.GeneralLinear (n + (j + k + 1) + 1) F where
  val := 1 + rectangularEntries j k x
  inv := 1 - rectangularEntries j k x
  val_inv := by
    simp [mul_sub, add_mul, rectangularEntries_sq]
  inv_val := by
    simp [sub_mul, mul_add, rectangularEntries_sq]

/-- The actual unequal-rank JPSS block matrix.
It is `diag(g,I_(j+k+1)) * (1 + X)`, hence has blocks
`[g,0,0; x,I_j,0; 0,0,I_(k+1)]`. -/
def unequalRankMatrix {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    Langlands.GeneralLinear (n + (j + k + 1) + 1) F :=
  appendIdentity n (j + k + 1) g * rectangularUnipotent j k x

omit [TopologicalSpace F] in
theorem appendIdentity_mul_rectangularEntries {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    (appendIdentity n (j + k + 1) g).val * rectangularEntries j k x =
      rectangularEntries j k x := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases ha : a.val < n + 1
  · have hr : ¬ (n + 1 ≤ a.val ∧ a.val < n + 1 + j) := by omega
    have he : rectangularEntries j k x a b = 0 := by
      simp only [rectangularEntries, dite_eq_right hr]
    rw [he]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c.val < n + 1
    · have hr' : ¬ (n + 1 ≤ c.val ∧ c.val < n + 1 + j) := by omega
      simp only [rectangularEntries, dite_eq_right hr', mul_zero]
    · rw [appendIdentity_entry]
      simp only [dite_eq_left ha, dite_eq_right hc, zero_mul]
  · simp_rw [appendIdentity_entry]
    simp [ha]

omit [TopologicalSpace F] in
/-- The block formula is checked as an equality of actual matrices, not merely
as a name for an unspecified embedding. -/
theorem unequalRankMatrix_val {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    (unequalRankMatrix j k g x).val =
      (appendIdentity n (j + k + 1) g).val + rectangularEntries j k x := by
  change (appendIdentity n (j + k + 1) g).val * (1 + rectangularEntries j k x) = _
  rw [mul_add, mul_one, appendIdentity_mul_rectangularEntries]

omit [TopologicalSpace F] in
/-- With no rectangular rows, the block matrix is the standard diagonal inclusion. -/
@[simp] theorem unequalRankMatrix_zero_rows {n : ℕ} (k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin 0) (Fin (n + 1)) F) :
    unequalRankMatrix 0 k g x = appendIdentity n (0 + k + 1) g := by
  apply Units.ext
  rw [unequalRankMatrix_val]
  have hz : rectangularEntries 0 k x = 0 := by
    ext a b
    simp [rectangularEntries]
  simp [hz]

omit [TopologicalSpace F] in
/-- Left multiplication on the small group acts on the leading large block.
The rectangular integration variable is unchanged. -/
theorem unequalRankMatrix_unipotent_mul {n : ℕ} (j k : ℕ)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    unequalRankMatrix j k (u.val * g) x =
      (appendUnipotent u (j + k + 1)).val * unequalRankMatrix j k g x := by
  simp [unequalRankMatrix, map_mul, mul_assoc]

/-- The unequal-rank JPSS function for every `j ≥ 0` and remaining gap `k ≥ 0`.
The large and small ranks differ by `j + k + 1`. -/
def unequalRankFunction (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (j k : ℕ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  W.val (unequalRankMatrix j k g x) * W'.val g *
    determinantWeight abv g (s - ((j + k + 1 : ℕ) : ℂ) / 2)

theorem unequalRankFunction_invariant (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (j k : ℕ)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankFunction ψ abv j k W W' s x (u.val * g) =
      unequalRankFunction ψ abv j k W W' s x g := by
  unfold unequalRankFunction
  rw [unequalRankMatrix_unipotent_mul, W.property, W'.property,
    appendUnipotent_character, determinantWeight_unipotent_mul]
  change ((standardCharacter ψ n u : ℂ) * W.val (unequalRankMatrix j k g x)) *
      ((((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * W'.val g) * _ = _
  rw [mul_mul_mul_comm (standardCharacter ψ n u : ℂ), ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

/-- The unequal-rank integrand, on the actual rectangular matrix space and
left-unipotent quotient, with representative independence proved. -/
def unequalRankIntegrand (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (j k : ℕ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) : LeftUnipotentQuotient n F → ℂ :=
  QuotientIntegration.descend _ (unequalRankFunction ψ abv j k W W' s x)
    (unequalRankFunction_invariant ψ abv j k W W' s x)

@[simp] theorem unequalRankIntegrand_mk (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (j k : ℕ)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankIntegrand ψ abv j k W W' s x (Quotient.mk _ g) =
      W.val (unequalRankMatrix j k g x) * W'.val g *
        determinantWeight abv g (s - ((j + k + 1 : ℕ) : ℂ) / 2) := rfl

/-- Absolute convergence on the product of quotient and rectangular matrix spaces.
Both measures are explicit; no normalization or existence of such a compatible
Haar pair is asserted here. -/
def UnequalRankConverges (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) : Prop :=
  Integrable (fun qx => unequalRankIntegrand ψ abv j k W W' s qx.2 qx.1) (μ.prod ν)

/-- The actual iterated unequal-rank JPSS scalar integral for all allowed blocks.
The rectangular variable is integrated first, as in the original formula. -/
def unequalRankIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) : ℂ :=
  ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W W' s x q ∂ν ∂μ

/-- The general block family reduces to the corank-one integrand when `j = k = 0`. -/
@[simp] theorem unequalRankIntegrand_zero_zero (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F) (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 0 W W' s x q = corankOneIntegrand ψ abv W W' s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp [unequalRankIntegrand_mk, corankOneIntegrand_mk,
      unequalRankMatrix_zero_rows, appendIdentity]

/-- The zero-dimensional rectangular variable carries unit mass. With that explicit
measure the general scalar integral agrees with the corank-one formula. -/
theorem unequalRankIntegral_zero_zero (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 0 μ (Measure.dirac 0) W W' s =
      corankOneIntegral ψ abv μ W W' s := by
  simp [unequalRankIntegral, corankOneIntegral]

section CoefficientModels

universe uV uV'

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']

/-- The equal-rank integral family on the actual coefficient images of the specified
representations and Whittaker functionals. -/
def equalRankModelIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (W : (coefficientModel π ℓ).toSubmodule) (W' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) : ℂ :=
  equalRankIntegral ψ abv μ W.val W'.val Φ s

/-- The corank-one family on actual coefficient-model vectors.
Spherical tests can be specified as fixed vectors in the second model. -/
def corankOneModelIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ (n + 1) π) (ℓ' : glInverseFunctionals ψ n σ)
    (W : (coefficientModel π ℓ).toSubmodule) (W' : (coefficientModel σ ℓ').toSubmodule)
    (s : ℂ) : ℂ :=
  corankOneIntegral ψ abv μ W.val W'.val s

/-- All unequal-rank blocks, now parameterized by actual coefficient-image vectors
of the two representations. This does not require selecting a preferred functional. -/
def unequalRankModelIntegral (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (W : (coefficientModel π ℓ).toSubmodule) (W' : (coefficientModel σ ℓ').toSubmodule)
    (s : ℂ) : ℂ :=
  unequalRankIntegral ψ abv j k μ ν W.val W'.val s

end CoefficientModels

end Langlands.RankinSelberg
