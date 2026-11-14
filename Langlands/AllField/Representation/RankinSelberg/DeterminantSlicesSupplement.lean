import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlices
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
/-!
# Determinant slices and equal-rank slice coefficients

JPSS (1983), Section 4.2, (4.2.1): the determinant fibers `|det g| = q^(-m)` of
the actual quotient `N_(n+1) \ GL_(n+1)` and the restricted integrals over them.
The measure is supplied. No convergence, support bound, compactness, or series
expansion of the full integral is asserted.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis
open _root_.MeasureTheory

universe uF

section General


end General

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- JPSS (4.2.1) quotient determinant order: `q ↦ ord(det g)` for any representative
`g` of `q ∈ N_(n+1) \ GL_(n+1)`. Independence uses `det u = 1` for upper unipotent `u`. -/
def determinantOrder (n : ℕ) : LeftUnipotentQuotient n F → ℤ :=
  QuotientIntegration.descend _
    (fun g : Langlands.GeneralLinear (n + 1) F =>
      T.ord (GeneralLinear.determinant g : F))
    (fun u g => by simp only [determinant_unipotent_mul])

@[simp] theorem determinantOrder_mk (n : ℕ) (g : Langlands.GeneralLinear (n + 1) F) :
    determinantOrder T n (Quotient.mk _ g) = T.ord (GeneralLinear.determinant g : F) :=
  rfl

/-- JPSS (4.2.1) determinant slice `N_(n+1) \ G^m`, where `G^m = {g | |det g| = q^(-m)}`,
written through the quotient determinant order. -/
def determinantSlice (n : ℕ) (m : ℤ) : Set (LeftUnipotentQuotient n F) :=
  {q | determinantOrder T n q = m}

theorem mem_determinantSlice {n : ℕ} {m : ℤ} {q : LeftUnipotentQuotient n F} :
    q ∈ determinantSlice T n m ↔ determinantOrder T n q = m :=
  Iff.rfl

theorem mk_mem_determinantSlice {n : ℕ} {m : ℤ} {g : Langlands.GeneralLinear (n + 1) F} :
    Quotient.mk _ g ∈ determinantSlice T n m ↔
      T.ord (GeneralLinear.determinant g : F) = m :=
  Iff.rfl

/-- Slice membership of a representative is the source condition `|det g| = q^(-m)`
for the residue-normalized absolute value. -/
theorem mk_mem_determinantSlice_iff_normalizedAbs {n : ℕ} {m : ℤ}
    {g : Langlands.GeneralLinear (n + 1) F} :
    Quotient.mk _ g ∈ determinantSlice T n m ↔
      T.normalizedAbs (GeneralLinear.determinant g : F) =
        (T.residueCardinality : ℝ) ^ (-m) := by
  rw [mk_mem_determinantSlice,
    T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  constructor
  · intro h
    rw [h]
  · intro h
    exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' h)

/-- The quotient determinant order is continuous into the discrete integers. -/
theorem continuous_determinantOrder (n : ℕ) :
    letI := T.topology
    Continuous (determinantOrder T n) := by
  let := T.topology
  exact Continuous.quotient_lift
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (n + 1)).continuous) _

theorem isClopen_determinantSlice (n : ℕ) (m : ℤ) :
    letI := T.topology
    IsClopen (determinantSlice T n m) := by
  let := T.topology
  exact (isClopen_discrete ({m} : Set ℤ)).preimage (continuous_determinantOrder T n)

theorem isOpen_determinantSlice (n : ℕ) (m : ℤ) :
    letI := T.topology
    IsOpen (determinantSlice T n m) := by
  let := T.topology
  exact (isClopen_determinantSlice T n m).isOpen

theorem isClosed_determinantSlice (n : ℕ) (m : ℤ) :
    letI := T.topology
    IsClosed (determinantSlice T n m) := by
  let := T.topology
  exact (isClopen_determinantSlice T n m).isClosed

/-- Every slice is measurable for any Borel structure on the actual quotient. -/
theorem measurableSet_determinantSlice (n : ℕ) (m : ℤ) :
    letI := T.topology
    ∀ [MeasurableSpace (LeftUnipotentQuotient n F)]
      [BorelSpace (LeftUnipotentQuotient n F)],
      MeasurableSet (determinantSlice T n m) := by
  let := T.topology
  intro _ _
  exact IsOpen.measurableSet (isOpen_determinantSlice T n m)

theorem disjoint_determinantSlice (n : ℕ) {m m' : ℤ} (h : m ≠ m') :
    Disjoint (determinantSlice T n m) (determinantSlice T n m') := by
  rw [Set.disjoint_left]
  intro q hq hq'
  exact h (hq.symm.trans hq')

theorem pairwise_disjoint_determinantSlice (n : ℕ) :
    Pairwise (Function.onFun Disjoint (determinantSlice T n)) :=
  fun _ _ h => disjoint_determinantSlice T n h

@[simp] theorem iUnion_determinantSlice (n : ℕ) :
    ⋃ m, determinantSlice T n m = Set.univ :=
  Set.eq_univ_of_forall fun q => Set.mem_iUnion.mpr ⟨determinantOrder T n q, rfl⟩

/-- Right translation by `g` shifts the quotient determinant order by `ord(det g)`. -/
theorem determinantOrder_rightTranslate (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (g : Langlands.GeneralLinear (n + 1) F) (q : LeftUnipotentQuotient n F),
      determinantOrder T n (QuotientIntegration.rightTranslate _ g q) =
        determinantOrder T n q + T.ord (GeneralLinear.determinant g : F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [QuotientIntegration.rightTranslate_mk, determinantOrder_mk, determinantOrder_mk,
      map_mul, Units.val_mul,
      T.ord_mul (GeneralLinear.determinant x).ne_zero (GeneralLinear.determinant g).ne_zero]

theorem rightTranslate_mem_determinantSlice (n : ℕ) (m : ℤ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (g : Langlands.GeneralLinear (n + 1) F) (q : LeftUnipotentQuotient n F),
      QuotientIntegration.rightTranslate _ g q ∈ determinantSlice T n m ↔
        q ∈ determinantSlice T n (m - T.ord (GeneralLinear.determinant g : F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro g q
  rw [mem_determinantSlice, mem_determinantSlice, determinantOrder_rightTranslate T n g q,
    eq_sub_iff_add_eq]

section Coefficients

/-! The quotient carries the Borel measurable structure of the quotient topology induced
by `T.topology`; the supplied measure `μ` is a measure for that structure. -/

variable {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  Measure (LeftUnipotentQuotient n F))

/-- The restricted coefficient `m ↦ ∫_{S_m} f dμ` over the determinant slices, for a
supplied measure on the Borel structure of the quotient. This is the general form of
JPSS (4.2.1). -/
def sliceCoefficient (f : LeftUnipotentQuotient n F → ℂ) (m : ℤ) : ℂ :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  ∫ q in determinantSlice T n m, f q ∂μ

/-- Integrability of `f` on the single slice `S_m`, for the Borel structure. -/
def SliceIntegrableAt (f : LeftUnipotentQuotient n F → ℂ) (m : ℤ) : Prop :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  IntegrableOn f (determinantSlice T n m) μ

theorem sliceIntegrableAt_iff (f : LeftUnipotentQuotient n F → ℂ) (m : ℤ) :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    SliceIntegrableAt T μ f m ↔ IntegrableOn f (determinantSlice T n m) μ :=
  Iff.rfl

/-- Integrability of `f` on every determinant slice, for the Borel structure. -/
def SliceIntegrable (f : LeftUnipotentQuotient n F → ℂ) : Prop :=
  ∀ m, SliceIntegrableAt T μ f m

variable {T μ}

/-- Global integrability implies integrability on every slice. -/
theorem sliceIntegrable_of_integrable {f : LeftUnipotentQuotient n F → ℂ} :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    Integrable f μ → SliceIntegrable T μ f := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  exact fun hf _ => hf.integrableOn

/-- Scalar multiplication needs no integrability hypothesis. -/
theorem sliceCoefficient_smul (c : ℂ) (f : LeftUnipotentQuotient n F → ℂ) (m : ℤ) :
    sliceCoefficient T μ (c • f) m = c * sliceCoefficient T μ f m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  exact integral_smul c f

variable (T μ)

/-- Each coefficient is the full integral of the indicator of the (Borel) slice. -/
theorem sliceCoefficient_eq_integral_indicator (f : LeftUnipotentQuotient n F → ℂ)
    (m : ℤ) :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    sliceCoefficient T μ f m = ∫ q, (determinantSlice T n m).indicator f q ∂μ := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  exact (integral_indicator (measurableSet_determinantSlice T n m)).symm

end Coefficients

section EqualRank

variable {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  Measure (LeftUnipotentQuotient n F))

/-- JPSS (4.2.1): `Ψ^m(W, W'; Φ) = ∫_{N \ G^m} W(g) W'(g) Φ(η g) dg`, realized as the
slice coefficient of the equal-rank integrand at `s = 0` for the normalized
absolute value. The measure `μ` is supplied on the Borel structure of the quotient. -/
def equalRankSliceCoefficient :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F), WhittakerFunctions ψ n →
      InverseWhittakerFunctions ψ n → SchwartzBruhat (Fin (n + 1) → F) → ℤ → ℂ := by
  letI := T.topology
  exact fun ψ W W' Φ =>
    sliceCoefficient T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0)

theorem equalRankSliceCoefficient_def :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    ∀ (ψ : UnitaryAdditiveCharacter F) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F))
      (m : ℤ),
      equalRankSliceCoefficient T μ ψ W W' Φ m =
        ∫ q in determinantSlice T n m,
          equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0 q ∂μ := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  intro ψ W W' Φ m
  rfl

/-- On the slice `S_m`, the integrand at `s` is its value at zero times
`(q^(-s))^m`, with `q` the residue cardinality and integer exponent `m`. -/
theorem equalRankIntegrand_eq_mul_spectralPoint_zpow :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F))
      (m : ℤ) (q : LeftUnipotentQuotient n F), q ∈ determinantSlice T n m →
      ∀ s : ℂ, equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s q =
        equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0 q *
          spectralPoint T.residueCardinality s ^ m := by
  let := T.topology
  intro ψ W W' Φ m q hq s
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [equalRankIntegrand_mk, equalRankIntegrand_mk, determinantWeight_zero, mul_one,
      normalizedDeterminantWeight_eq_spectralPoint_zpow]
    exact congrArg (fun k : ℤ => W.val g * W'.val g * Φ (lastRow g) *
      spectralPoint T.residueCardinality s ^ k) hq

/-- The restricted integral at `s` over `S_m` is the `m`-th coefficient times
`(q^(-s))^m`. No integrability is needed for this identity of Bochner integrals. -/
theorem setIntegral_equalRankIntegrand_determinantSlice :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    ∀ (ψ : UnitaryAdditiveCharacter F) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F))
      (m : ℤ) (s : ℂ),
      ∫ q in determinantSlice T n m,
          equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s q ∂μ =
        equalRankSliceCoefficient T μ ψ W W' Φ m *
          spectralPoint T.residueCardinality s ^ m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ W W' Φ m s
  rw [setIntegral_congr_fun (measurableSet_determinantSlice T n m)
    (fun q hq => equalRankIntegrand_eq_mul_spectralPoint_zpow T ψ W W' Φ m q hq s),
    integral_mul_const]
  rfl

/-- Slice integrability of the integrand at `s` is equivalent to that at zero. -/
theorem sliceIntegrableAt_equalRankIntegrand_iff :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F))
      (m : ℤ) (s : ℂ),
      SliceIntegrableAt T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s) m ↔
        SliceIntegrableAt T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ W W' Φ m s
  have hq : (T.residueCardinality : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.zero_lt_one.trans T.residueCardinality_gt_one).ne'
  have hc : spectralPoint T.residueCardinality s ^ m ≠ 0 := by
    apply zpow_ne_zero
    intro h
    exact hq ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [sliceIntegrableAt_iff, sliceIntegrableAt_iff,
    integrableOn_congr_fun
      (fun q hq => equalRankIntegrand_eq_mul_spectralPoint_zpow T ψ W W' Φ m q hq s)
      (measurableSet_determinantSlice T n m)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hc) _

end EqualRank

end Padic

end Langlands.AllField.RankinSelberg
