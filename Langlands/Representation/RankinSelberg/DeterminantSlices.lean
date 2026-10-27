import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.Group.GL.Padic

/-!
# Determinant slices and equal-rank slice coefficients

JPSS (1983), Section 4.2, (4.2.1): the determinant fibers `|det g| = q^(-m)` of
the actual quotient `N_(n+1) \ GL_(n+1)` and the restricted integrals over them.
The measure is supplied. No convergence, support bound, compactness, or series
expansion of the full integral is asserted.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory

universe uF

section General

variable {F : Type uF} [Field F]

/-- Left upper-unipotent multiplication preserves the actual determinant. -/
@[simp] theorem determinant_unipotent_mul {n : ℕ} (u : upperUnipotent n F)
    (g : Langlands.GeneralLinear n F) :
    GeneralLinear.determinant (u.val * g) = GeneralLinear.determinant g := by
  have hu : GeneralLinear.determinant u.val = 1 := Units.ext (unipotent_det u)
  rw [map_mul, hu, one_mul]

/-- The determinant weight at `s = 0` is one, for every absolute value. -/
@[simp] theorem determinantWeight_zero (abv : AbsoluteValue F ℝ) {n : ℕ}
    (g : Langlands.GeneralLinear n F) : determinantWeight abv g 0 = 1 :=
  Complex.cpow_zero _

/-- The representative value of the equal-rank integrand at `s = 0` is
`W(g) W'(g) Φ(lastRow g)`, the integrand of JPSS (4.2.1). -/
theorem equalRankIntegrand_zero_mk [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (g : Langlands.GeneralLinear (n + 1) F) :
    equalRankIntegrand ψ abv W W' Φ 0 (Quotient.mk _ g) =
      W.val g * W'.val g * Φ (lastRow g) := by
  rw [equalRankIntegrand_mk, determinantWeight_zero, mul_one]

end General

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The normalized order is continuous from the field units into the discrete integers. -/
theorem continuous_ord_units :
    letI := T.topology
    Continuous (fun a : F.Carrierˣ => T.ord (a : F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [continuous_discrete_rng]
  intro m
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  refine ⟨(fun x : F.Carrierˣ => x * a⁻¹) ⁻¹' (T.normalizedAbsUnits.ker : Set F.Carrierˣ),
    ?_, T.isOpen_ker_normalizedAbsUnits.preimage (continuous_id.mul continuous_const), ?_⟩
  · intro x hx
    have hk : x * a⁻¹ ∈ T.ordUnits.ker := by
      rw [T.ker_ordUnits]
      exact hx
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    have he := congrArg Multiplicative.toAdd hk
    rw [T.ordUnits_apply, T.ordUnits_apply] at he
    exact he.trans ha
  · change a * a⁻¹ ∈ T.normalizedAbsUnits.ker
    rw [mul_inv_cancel]
    exact T.normalizedAbsUnits.ker.one_mem

/-- JPSS (4.2.1) quotient determinant order: `q ↦ ord(det g)` for any representative
`g` of `q ∈ N_(n+1) \ GL_(n+1)`. Independence uses `det u = 1` for upper unipotent `u`. -/
def determinantOrder (n : ℕ) : LeftUnipotentQuotient n F.Carrier → ℤ :=
  QuotientIntegration.descend _
    (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      T.ord (GeneralLinear.determinant g : F.Carrier))
    (fun u g => by simp only [determinant_unipotent_mul])

@[simp] theorem determinantOrder_mk (n : ℕ) (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    determinantOrder T n (Quotient.mk _ g) = T.ord (GeneralLinear.determinant g : F.Carrier) :=
  rfl

/-- JPSS (4.2.1) determinant slice `N_(n+1) \ G^m`, where `G^m = {g | |det g| = q^(-m)}`,
written through the quotient determinant order. -/
def determinantSlice (n : ℕ) (m : ℤ) : Set (LeftUnipotentQuotient n F.Carrier) :=
  {q | determinantOrder T n q = m}

theorem mem_determinantSlice {n : ℕ} {m : ℤ} {q : LeftUnipotentQuotient n F.Carrier} :
    q ∈ determinantSlice T n m ↔ determinantOrder T n q = m :=
  Iff.rfl

theorem mk_mem_determinantSlice {n : ℕ} {m : ℤ} {g : Langlands.GeneralLinear (n + 1) F.Carrier} :
    Quotient.mk _ g ∈ determinantSlice T n m ↔
      T.ord (GeneralLinear.determinant g : F.Carrier) = m :=
  Iff.rfl

/-- Slice membership of a representative is the source condition `|det g| = q^(-m)`
for the residue-normalized absolute value. -/
theorem mk_mem_determinantSlice_iff_normalizedAbs {n : ℕ} {m : ℤ}
    {g : Langlands.GeneralLinear (n + 1) F.Carrier} :
    Quotient.mk _ g ∈ determinantSlice T n m ↔
      T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) =
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
    ∀ [MeasurableSpace (LeftUnipotentQuotient n F.Carrier)]
      [BorelSpace (LeftUnipotentQuotient n F.Carrier)],
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
    ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) (q : LeftUnipotentQuotient n F.Carrier),
      determinantOrder T n (QuotientIntegration.rightTranslate _ g q) =
        determinantOrder T n q + T.ord (GeneralLinear.determinant g : F.Carrier) := by
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
    ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) (q : LeftUnipotentQuotient n F.Carrier),
      QuotientIntegration.rightTranslate _ g q ∈ determinantSlice T n m ↔
        q ∈ determinantSlice T n (m - T.ord (GeneralLinear.determinant g : F.Carrier)) := by
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
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  Measure (LeftUnipotentQuotient n F.Carrier))

/-- The restricted coefficient `m ↦ ∫_{S_m} f dμ` over the determinant slices, for a
supplied measure on the Borel structure of the quotient. This is the general form of
JPSS (4.2.1). -/
def sliceCoefficient (f : LeftUnipotentQuotient n F.Carrier → ℂ) (m : ℤ) : ℂ :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  ∫ q in determinantSlice T n m, f q ∂μ

theorem sliceCoefficient_def (f : LeftUnipotentQuotient n F.Carrier → ℂ) (m : ℤ) :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    sliceCoefficient T μ f m = ∫ q in determinantSlice T n m, f q ∂μ :=
  rfl

/-- Integrability of `f` on the single slice `S_m`, for the Borel structure. -/
def SliceIntegrableAt (f : LeftUnipotentQuotient n F.Carrier → ℂ) (m : ℤ) : Prop :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  IntegrableOn f (determinantSlice T n m) μ

theorem sliceIntegrableAt_iff (f : LeftUnipotentQuotient n F.Carrier → ℂ) (m : ℤ) :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    SliceIntegrableAt T μ f m ↔ IntegrableOn f (determinantSlice T n m) μ :=
  Iff.rfl

/-- Integrability of `f` on every determinant slice, for the Borel structure. -/
def SliceIntegrable (f : LeftUnipotentQuotient n F.Carrier → ℂ) : Prop :=
  ∀ m, SliceIntegrableAt T μ f m

variable {T μ}

theorem SliceIntegrableAt.add {f g : LeftUnipotentQuotient n F.Carrier → ℂ} {m : ℤ}
    (hf : SliceIntegrableAt T μ f m) (hg : SliceIntegrableAt T μ g m) :
    SliceIntegrableAt T μ (f + g) m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact Integrable.add hf hg

theorem SliceIntegrableAt.smul {f : LeftUnipotentQuotient n F.Carrier → ℂ} {m : ℤ}
    (c : ℂ) (hf : SliceIntegrableAt T μ f m) : SliceIntegrableAt T μ (c • f) m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact Integrable.smul c hf

theorem SliceIntegrable.add {f g : LeftUnipotentQuotient n F.Carrier → ℂ}
    (hf : SliceIntegrable T μ f) (hg : SliceIntegrable T μ g) :
    SliceIntegrable T μ (f + g) :=
  fun m => (hf m).add (hg m)

theorem SliceIntegrable.smul {f : LeftUnipotentQuotient n F.Carrier → ℂ}
    (c : ℂ) (hf : SliceIntegrable T μ f) : SliceIntegrable T μ (c • f) :=
  fun m => (hf m).smul c

/-- Global integrability implies integrability on every slice. -/
theorem sliceIntegrable_of_integrable {f : LeftUnipotentQuotient n F.Carrier → ℂ} :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    Integrable f μ → SliceIntegrable T μ f := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact fun hf _ => hf.integrableOn

theorem sliceCoefficient_add {f g : LeftUnipotentQuotient n F.Carrier → ℂ} {m : ℤ}
    (hf : SliceIntegrableAt T μ f m) (hg : SliceIntegrableAt T μ g m) :
    sliceCoefficient T μ (f + g) m = sliceCoefficient T μ f m + sliceCoefficient T μ g m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact integral_add hf hg

/-- Scalar multiplication needs no integrability hypothesis. -/
theorem sliceCoefficient_smul (c : ℂ) (f : LeftUnipotentQuotient n F.Carrier → ℂ) (m : ℤ) :
    sliceCoefficient T μ (c • f) m = c * sliceCoefficient T μ f m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact integral_smul c f

/-- Coefficientwise additivity of the coefficient functions `ℤ → ℂ`. -/
theorem sliceCoefficient_add_fun {f g : LeftUnipotentQuotient n F.Carrier → ℂ}
    (hf : SliceIntegrable T μ f) (hg : SliceIntegrable T μ g) :
    sliceCoefficient T μ (f + g) = sliceCoefficient T μ f + sliceCoefficient T μ g :=
  funext fun m => sliceCoefficient_add (hf m) (hg m)

theorem sliceCoefficient_smul_fun (c : ℂ) (f : LeftUnipotentQuotient n F.Carrier → ℂ) :
    sliceCoefficient T μ (c • f) = c • sliceCoefficient T μ f :=
  funext fun m => sliceCoefficient_smul c f m

variable (T μ)

/-- Each coefficient is the full integral of the indicator of the (Borel) slice. -/
theorem sliceCoefficient_eq_integral_indicator (f : LeftUnipotentQuotient n F.Carrier → ℂ)
    (m : ℤ) :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    sliceCoefficient T μ f m = ∫ q, (determinantSlice T n m).indicator f q ∂μ := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  exact (integral_indicator (measurableSet_determinantSlice T n m)).symm

end Coefficients

section EqualRank

variable {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  Measure (LeftUnipotentQuotient n F.Carrier))

/-- JPSS (4.2.1): `Ψ^m(W, W'; Φ) = ∫_{N \ G^m} W(g) W'(g) Φ(η g) dg`, realized as the
slice coefficient of the equal-rank integrand at `s = 0` for the normalized
absolute value. The measure `μ` is supplied on the Borel structure of the quotient. -/
def equalRankSliceCoefficient :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier), WhittakerFunctions ψ n →
      InverseWhittakerFunctions ψ n → SchwartzBruhat (Fin (n + 1) → F.Carrier) → ℤ → ℂ := by
  letI := T.topology
  exact fun ψ W W' Φ =>
    sliceCoefficient T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0)

theorem equalRankSliceCoefficient_def :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (m : ℤ),
      equalRankSliceCoefficient T μ ψ W W' Φ m =
        ∫ q in determinantSlice T n m,
          equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0 q ∂μ := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ m
  rfl

/-- On the slice `S_m`, the integrand at `s` is its value at zero times
`(q^(-s))^m`, with `q` the residue cardinality and integer exponent `m`. -/
theorem equalRankIntegrand_eq_mul_spectralPoint_zpow :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (m : ℤ) (q : LeftUnipotentQuotient n F.Carrier), q ∈ determinantSlice T n m →
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
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (m : ℤ) (s : ℂ),
      ∫ q in determinantSlice T n m,
          equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s q ∂μ =
        equalRankSliceCoefficient T μ ψ W W' Φ m *
          spectralPoint T.residueCardinality s ^ m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ W W' Φ m s
  rw [setIntegral_congr_fun (measurableSet_determinantSlice T n m)
    (fun q hq => equalRankIntegrand_eq_mul_spectralPoint_zpow T ψ W W' Φ m q hq s),
    integral_mul_const]
  rfl

/-- Slice integrability of the integrand at `s` is equivalent to that at zero. -/
theorem sliceIntegrableAt_equalRankIntegrand_iff :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n)
      (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (m : ℤ) (s : ℂ),
      SliceIntegrableAt T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s) m ↔
        SliceIntegrableAt T μ (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) m := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
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

end Langlands.RankinSelberg
