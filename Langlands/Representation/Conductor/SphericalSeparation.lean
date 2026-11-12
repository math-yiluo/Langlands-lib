import Langlands.Representation.Conductor.SchurIndependence
import Langlands.Representation.Conductor.SphericalSeries
import Langlands.Analysis.Local.QuotientMass
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells

/-!
# Separation by the spherical Laurent coefficients

Let `w` be a vector of the Whittaker model of a smooth representation of
`GL_(n+2)(F)` whose restriction to `diag(GL_(n+1), 1)` is right
`GL_(n+1)(O)`-invariant. If every Laurent degree coefficient
`degreeCorankOneModelCoefficient` of its corank-one integral against the spherical
Whittaker functions vanishes, then `w` vanishes on `diag(GL_(n+1), 1)`.

Each degree coefficient is a finite sum over the Iwasawa cells
`N \ N ϖ^lam GL_(n+1)(O)` of the cell mass times the Laurent-valued integrand at
`ϖ^lam`. For a dominant `lam` that value is a nonzero multiple of
`W(diag(ϖ^lam, 1))` times the Schur expression of `lam`, and it vanishes otherwise.
Linear independence of the Schur expressions separates the dominant values, and the
`ψ`-equivariance kills the non-dominant ones.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa
open Langlands.GeneralLinear.Spherical
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

universe uF uV

section Cells

variable {F : Type uF} [Field F] [ValuativeRel F] {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The Iwasawa exponent, descended to the left-unipotent quotient. -/
def quotientExponent : LeftUnipotentQuotient n F → Fin (n + 1) → ℤ :=
  descend _ (exponent hϖ) (fun u g => exponent_unipotent_mul hϖ g u.property)

@[simp] theorem quotientExponent_mk (g : Langlands.GeneralLinear (n + 1) F) :
    quotientExponent hϖ (Quotient.mk _ g) = exponent hϖ g := rfl

theorem sphericalQuotientDegree_eq_sum (t : LeftUnipotentQuotient n F) :
    sphericalQuotientDegree hϖ t = ∑ i, quotientExponent hϖ t i := by
  induction t using Quotient.inductionOn with
  | h g => rfl

/-- The Iwasawa cell `N \ N ϖ^lam GL_(n+1)(O)` of the left-unipotent quotient. -/
def sphericalCell (lam : Fin (n + 1) → ℤ) : Set (LeftUnipotentQuotient n F) :=
  quotientExponent hϖ ⁻¹' {lam}

theorem mem_sphericalCell_iff {lam : Fin (n + 1) → ℤ} {t : LeftUnipotentQuotient n F} :
    t ∈ sphericalCell hϖ lam ↔ quotientExponent hϖ t = lam := Iff.rfl

/-- The cell is the image of the translate `ϖ^lam GL_(n+1)(O)`. -/
theorem sphericalCell_eq_image (lam : Fin (n + 1) → ℤ) :
    sphericalCell hϖ lam =
      (fun k => leftQuotientMap (upperUnipotent (n + 1) F) (torus ϖ lam * k)) ''
        (integralSubgroup (ValuativeRel.valuation F).integer n :
          Set (Langlands.GeneralLinear (n + 1) F)) := by
  ext t
  induction t using Quotient.inductionOn with
  | h g =>
    constructor
    · intro hg
      change exponent hϖ g = lam at hg
      obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent hϖ g
      refine ⟨k, hk, ?_⟩
      apply Quotient.sound
      change QuotientGroup.rightRel (upperUnipotent (n + 1) F) (torus ϖ lam * k) g
      rw [QuotientGroup.rightRel_apply]
      have hu' : g * (torus ϖ lam * k)⁻¹ = u := by
        rw [heq, hg, mul_assoc u, mul_inv_cancel_right]
      rw [hu']
      exact hu
    · rintro ⟨k, hk, hkg⟩
      have he := congrArg (quotientExponent hϖ) hkg
      change exponent hϖ (torus ϖ lam * k) = exponent hϖ g at he
      change exponent hϖ g = lam
      rw [← he]
      exact exponent_eq hϖ (one_mem _) hk (by rw [one_mul])

theorem sphericalCell_nonempty (lam : Fin (n + 1) → ℤ) :
    (sphericalCell hϖ lam).Nonempty :=
  ⟨Quotient.mk _ (torus ϖ lam), exponent_torus hϖ lam⟩

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isOpen_sphericalCell (lam : Fin (n + 1) → ℤ) :
    IsOpen (sphericalCell hϖ lam) := by
  rw [sphericalCell_eq_image, show (fun k => leftQuotientMap (upperUnipotent (n + 1) F)
      (torus ϖ lam * k)) = leftQuotientMap (upperUnipotent (n + 1) F) ∘
        (fun k => torus ϖ lam * k) from rfl, Set.image_comp]
  exact (leftQuotient_isOpenQuotientMap _).isOpenMap _
    (isOpenMap_mul_left (torus ϖ lam) _
      (isOpen_integralSubgroup _ n (Valuation.isOpen_integer (v := ValuativeRel.valuation F))))

theorem isCompact_sphericalCell (lam : Fin (n + 1) → ℤ) :
    IsCompact (sphericalCell hϖ lam) := by
  have hK : IsCompact (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) := by
    have hk := isCompact_levelOpenSubgroup F n 0
    change IsCompact (levelSubgroup F n 0 :
      Set (Langlands.GeneralLinear (n + 1) F)) at hk
    rwa [levelSubgroup_zero] at hk
  rw [sphericalCell_eq_image]
  exact hK.image ((leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).continuous.comp (continuous_const.mul continuous_id))

end Cells

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The standard character at the adjacent elementary matrix `1 + t E_(i,i+1)`. -/
theorem standardCharacter_adjacentUnit_val (ψ : UnitaryAdditiveCharacter F)
    {r : ℕ} (i : Fin r) (t : F) :
    (standardCharacter ψ r (adjacentUnit i t) : ℂ) = ψ.complex t := by
  rw [standardCharacter_apply]
  congr 1
  change (∑ j : Fin r, Matrix.transvection i.castSucc i.succ t j.castSucc j.succ) = t
  have hentry (j : Fin r) :
      Matrix.transvection i.castSucc i.succ t j.castSucc j.succ = if j = i then t else 0 := by
    simp [Matrix.transvection, Matrix.single_apply, ne_of_lt j.castSucc_lt_succ, eq_comm]
  simp_rw [hentry]
  simp

end Character

section Model

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- Every Iwasawa cell has positive finite mass for a Jacquet-normalized measure. -/
theorem sphericalCell_measure (lam : Fin (n + 1) → ℤ) :
    0 < μ (sphericalCell h.uniformizer lam) ∧ μ (sphericalCell h.uniformizer lam) < ⊤ := by
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  exact h.measure.measure_pos_lt_top (isCompact_sphericalCell h.uniformizer lam)
    (isOpen_sphericalCell h.uniformizer lam) (sphericalCell_nonempty h.uniformizer lam)

include h in
/-- The residue cardinality of a Jacquet normalization is nonzero. -/
theorem IsJacquetNormalization.residueCardinality_ne_zero : q ≠ 0 := by
  intro hq
  have h1 := h.abv_uniformizer
  rw [hq, Nat.cast_zero, inv_zero] at h1
  exact (abv.pos ϖ.ne_zero).ne' h1

/-- The Laurent-valued corank-one function of `w` at the torus point `ϖ^lam`. -/
def cellCorankOneValue (lam : Fin (n + 1) → ℤ) : symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  corankOnePolynomialFunction ψ abv h.uniformizer q w.val (torus ϖ lam)

/-- Under restriction invariance, the Laurent-valued corank-one function is right
`GL_(n+1)(O)`-invariant. -/
theorem corankOnePolynomialFunction_mul_integral
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (g k : Langlands.GeneralLinear (n + 1) F)
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    corankOnePolynomialFunction ψ abv h.uniformizer q w.val (g * k) =
      corankOnePolynomialFunction ψ abv h.uniformizer q w.val g := by
  have hW : w.val.val (rankInclusion 1 (g * k)) = w.val.val (rankInclusion 1 g) :=
    hw g ⟨k, hk⟩
  unfold corankOnePolynomialFunction
  rw [hW, determinantWeight_mul_integral h.abv_unit g k hk,
    sphericalWhittakerPolynomial_mul_integral h.uniformizer _ q
      (isIntegrallyTrivial_inverseStandardCharacter h.conductor.1 n) g hk]

/-- On the quotient, the Laurent-valued integrand is constant on each cell. -/
theorem corankOnePolynomialIntegrand_eq_cellValue
    (hw : IsIntegralInvariantOnRestriction π ℓ w) (t : LeftUnipotentQuotient n F) :
    corankOnePolynomialIntegrand ψ abv h.uniformizer q w.val h.conductor.1 t =
      cellCorankOneValue h π ℓ w (quotientExponent h.uniformizer t) := by
  induction t using Quotient.inductionOn with
  | h g =>
    obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent h.uniformizer g
    have heq' : g = (⟨u, hu⟩ : upperUnipotent (n + 1) F).val *
        (torus ϖ (exponent h.uniformizer g) * k) := by
      simpa only [mul_assoc] using heq
    rw [corankOnePolynomialIntegrand_mk, quotientExponent_mk, cellCorankOneValue]
    conv_lhs => rw [heq']
    rw [corankOnePolynomialFunction_invariant ψ abv h.uniformizer q w.val h.conductor.1,
      corankOnePolynomialFunction_mul_integral h π ℓ w hw _ k hk]

/-- The value at a dominant torus point. -/
theorem cellCorankOneValue_of_antitone {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) :
    cellCorankOneValue h π ℓ w lam =
      (w.val.val (rankInclusion 1 (torus ϖ lam)) *
        determinantWeight abv (torus ϖ lam) (0 - 1 / 2) * halfModulus q lam) •
        symmetricTorusSchur ℂ lam := by
  rw [cellCorankOneValue, corankOnePolynomialFunction,
    sphericalWhittakerPolynomial_torus h.uniformizer _ q
      (isIntegrallyTrivial_inverseStandardCharacter h.conductor.1 n),
    ite_eq_left hlam, ← Algebra.smul_def, smul_smul]

/-- The value at a non-dominant torus point vanishes. -/
theorem cellCorankOneValue_of_not_antitone {lam : Fin (n + 1) → ℤ}
    (hlam : ¬ Antitone lam) : cellCorankOneValue h π ℓ w lam = 0 := by
  rw [cellCorankOneValue, corankOnePolynomialFunction,
    sphericalWhittakerPolynomial_torus h.uniformizer _ q
      (isIntegrallyTrivial_inverseStandardCharacter h.conductor.1 n),
    ite_eq_right hlam, smul_zero]

/-- Each degree integrand is a finite sum of constants on the cells of that degree
above the common lower bound of the nonzero exponents. -/
theorem degreeCorankOneModelIntegrand_eq_sum
    (hw : IsIntegralInvariantOnRestriction π ℓ w) (b : ℤ)
    (hb : ∀ g : Langlands.GeneralLinear (n + 1) F,
      corankOnePolynomialFunction ψ abv h.uniformizer q w.val g ≠ 0 →
        ∀ i, b ≤ exponent h.uniformizer g i)
    (d : ℤ) (t : LeftUnipotentQuotient n F) :
    degreeCorankOneModelIntegrand h π ℓ w d t =
      ∑ lam ∈ (boundedDegreeExponents_finite n b d).toFinset,
        (sphericalCell h.uniformizer lam).indicator
          (fun _ => cellCorankOneValue h π ℓ w lam) t := by
  classical
  simp only [Set.indicator_apply, mem_sphericalCell_iff]
  rw [Finset.sum_ite_eq]
  unfold degreeCorankOneModelIntegrand degreeCorankOnePolynomialIntegrand
  rw [sphericalQuotientDegree_eq_sum, corankOnePolynomialIntegrand_eq_cellValue h π ℓ w hw]
  set lam := quotientExponent h.uniformizer t
  by_cases hS : lam ∈ (boundedDegreeExponents_finite n b d).toFinset
  · rw [ite_eq_left hS, ite_eq_left ((Set.Finite.mem_toFinset _).mp hS).2]
  · rw [ite_eq_right hS]
    split_ifs with hd
    · by_contra hne
      apply hS
      refine (Set.Finite.mem_toFinset _).mpr ⟨fun i => ?_, hd⟩
      have := hb (torus ϖ lam) hne i
      rwa [exponent_torus] at this
    · rfl

/-- Each Laurent degree coefficient is the sum over the cells of that degree of the
cell mass times the cell value. -/
theorem degreeCorankOneModelCoefficient_eq_sum
    (hw : IsIntegralInvariantOnRestriction π ℓ w) (b : ℤ)
    (hb : ∀ g : Langlands.GeneralLinear (n + 1) F,
      corankOnePolynomialFunction ψ abv h.uniformizer q w.val g ≠ 0 →
        ∀ i, b ≤ exponent h.uniformizer g i)
    (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ w d =
      ∑ lam ∈ (boundedDegreeExponents_finite n b d).toFinset,
        ((μ.real (sphericalCell h.uniformizer lam) : ℝ) : ℂ) •
          cellCorankOneValue h π ℓ w lam := by
  classical
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_degreeCorankOneModelCoefficient, map_sum]
  have hpt : ∀ t, (if sphericalQuotientDegree h.uniformizer t = d then
      corankOneIntegrand ψ abv w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) 0 t else 0) =
      ∑ lam ∈ (boundedDegreeExponents_finite n b d).toFinset,
        (sphericalCell h.uniformizer lam).indicator
          (fun _ => symmetricTorusEvaluation (Fin (n + 1)) ℂ x
            (cellCorankOneValue h π ℓ w lam)) t := by
    intro t
    rw [← symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand ψ abv h.uniformizer q
      w.val h.conductor.1 x d t]
    change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ w d t) = _
    rw [degreeCorankOneModelIntegrand_eq_sum h π ℓ w hw b hb d t, map_sum]
    refine Finset.sum_congr rfl (fun lam _ => ?_)
    by_cases ht : t ∈ sphericalCell h.uniformizer lam
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, map_zero]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun lam _ =>
    (integrableOn_const (sphericalCell_measure h lam).2.ne).integrable_indicator
      (isOpen_sphericalCell h.uniformizer lam).measurableSet)]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [integral_indicator_const _ (isOpen_sphericalCell h.uniformizer lam).measurableSet,
    map_smul, smul_eq_mul, Complex.real_smul]

include h in
/-- The half-modulus factor never vanishes. -/
theorem halfModulus_ne_zero (lam : Fin (n + 1) → ℤ) : halfModulus q lam ≠ 0 := by
  apply zpow_ne_zero
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h.residueCardinality_ne_zero)))

/-- If every Laurent degree coefficient vanishes, `w` vanishes at every dominant torus
point of `diag(GL_(n+1), 1)`. -/
theorem torus_eq_zero_of_antitone_of_degreeCoefficients_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hzero : ∀ d, degreeCorankOneModelCoefficient h π hπ ℓ w d = 0)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) :
    w.val.val (rankInclusion 1 (torus ϖ lam)) = 0 := by
  classical
  obtain ⟨b, hb⟩ := model_corankOne_polynomial_exponents_lower_bound h.uniformizer π hπ ψ ℓ
    abv q h.conductor w
  by_contra hW
  set d : ℤ := ∑ i, lam i
  set S := (boundedDegreeExponents_finite n b d).toFinset
  let c : {lam : Fin (n + 1) → ℤ // Antitone lam} → ℂ := fun ν =>
    ((μ.real (sphericalCell h.uniformizer ν.val) : ℝ) : ℂ) *
      (w.val.val (rankInclusion 1 (torus ϖ ν.val)) *
        determinantWeight abv (torus ϖ ν.val) (0 - 1 / 2) * halfModulus q ν.val)
  let f : (Fin (n + 1) → ℤ) → symmetricTorusSubalgebra (Fin (n + 1)) ℂ := fun lam' =>
    if Antitone lam' then
      (((μ.real (sphericalCell h.uniformizer lam') : ℝ) : ℂ) *
        (w.val.val (rankInclusion 1 (torus ϖ lam')) *
          determinantWeight abv (torus ϖ lam') (0 - 1 / 2) * halfModulus q lam')) •
        symmetricTorusSchur ℂ lam'
    else 0
  have hsum : ∑ ν ∈ S.subtype Antitone, c ν • symmetricTorusSchur ℂ ν.val = 0 := by
    have h1 : ∑ ν ∈ S.subtype Antitone, c ν • symmetricTorusSchur ℂ ν.val =
        ∑ ν ∈ S.subtype Antitone, f ν.val := by
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      dsimp only [f, c]
      rw [ite_eq_left ν.property]
    have h2 : ∑ lam' ∈ S, f lam' = degreeCorankOneModelCoefficient h π hπ ℓ w d := by
      rw [degreeCorankOneModelCoefficient_eq_sum h π hπ ℓ w hw b hb d]
      refine Finset.sum_congr rfl (fun lam' _ => ?_)
      dsimp only [f]
      by_cases ha : Antitone lam'
      · rw [ite_eq_left ha, cellCorankOneValue_of_antitone h π ℓ w ha, smul_smul]
      · rw [ite_eq_right ha, cellCorankOneValue_of_not_antitone h π ℓ w ha, smul_zero]
    have h3 : ∀ lam' ∈ S, f lam' ≠ 0 → Antitone lam' := by
      intro lam' _ hf
      by_contra ha
      apply hf
      dsimp only [f]
      rw [ite_eq_right ha]
    rw [h1, Finset.sum_subtype_eq_sum_filter, Finset.sum_filter_of_ne h3, h2, hzero d]
  have hcoef : w.val.val (rankInclusion 1 (torus ϖ lam)) *
      determinantWeight abv (torus ϖ lam) (0 - 1 / 2) * halfModulus q lam ≠ 0 :=
    mul_ne_zero (mul_ne_zero hW (determinantWeight_ne_zero abv _ _)) (halfModulus_ne_zero h lam)
  have hmem : (⟨lam, hlam⟩ : {lam : Fin (n + 1) → ℤ // Antitone lam}) ∈
      S.subtype Antitone := by
    rw [Finset.mem_subtype]
    refine (Set.Finite.mem_toFinset _).mpr ⟨fun i => ?_, rfl⟩
    have hne : corankOnePolynomialFunction ψ abv h.uniformizer q w.val (torus ϖ lam) ≠ 0 := by
      change cellCorankOneValue h π ℓ w lam ≠ 0
      rw [cellCorankOneValue_of_antitone h π ℓ w hlam]
      intro hz
      apply (symmetricTorusSchur_linearIndependent ℂ n).ne_zero ⟨lam, hlam⟩
      have := congrArg (fun z => (w.val.val (rankInclusion 1 (torus ϖ lam)) *
        determinantWeight abv (torus ϖ lam) (0 - 1 / 2) * halfModulus q lam)⁻¹ • z) hz
      simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul, smul_zero] using this
    have := hb (torus ϖ lam) hne i
    rwa [exponent_torus] at this
  have hc := linearIndependent_iff'.mp (symmetricTorusSchur_linearIndependent ℂ n)
    (S.subtype Antitone) c hsum ⟨lam, hlam⟩ hmem
  have hmass : (0 : ℝ) < μ.real (sphericalCell h.uniformizer lam) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (sphericalCell_measure h lam).1.ne'
      (sphericalCell_measure h lam).2.ne
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hmass.ne') hcoef hc

include h in
/-- The model function vanishes at every non-dominant torus point of
`diag(GL_(n+1), 1)`. -/
theorem torus_eq_zero_of_not_antitone_of_restriction
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    {lam : Fin (n + 1) → ℤ} (hlam : ¬ Antitone lam) :
    w.val.val (rankInclusion 1 (torus ϖ lam)) = 0 := by
  have hf : ∀ (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F),
      w.val.val (rankInclusion 1 (u.val * g)) =
        (standardCharacter ψ n u : ℂ) * w.val.val (rankInclusion 1 g) := by
    intro u g
    rw [map_mul]
    change w.val.val ((corankOneUnipotent u).val * rankInclusion 1 g) = _
    rw [w.val.property, corankOne_standardCharacter]
  have hK : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        w.val.val (rankInclusion 1 (g * k)) = w.val.val (rankInclusion 1 g) :=
    fun g k hk => hw g ⟨k, hk⟩
  have hθ : ∀ i : Fin n, ∃ x : F,
      ValuativeRel.valuation F x * ValuativeRel.valuation F (ϖ : F) ≤ 1 ∧
        standardCharacter ψ n (adjacentUnit i x) ≠ 1 := by
    intro i
    have hv0 : 0 < ValuativeRel.valuation F (ϖ : F) :=
      valuation_pos (ValuativeRel.valuation F) ϖ
    have hnot : ((ϖ : F))⁻¹ ∉ (ValuativeRel.valuation F).integer := by
      rw [Valuation.mem_integer_iff, map_inv₀, not_le]
      exact one_lt_inv_iff₀.mpr ⟨hv0, h.uniformizer.1⟩
    have hex : ∃ y ∈ (ValuativeRel.valuation F).integer, ψ ((ϖ : F)⁻¹ * y) ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hnot (h.conductor.2 _ hall)
    obtain ⟨y, hy, hψy⟩ := hex
    refine ⟨(ϖ : F)⁻¹ * y, ?_, ?_⟩
    · rw [map_mul, map_inv₀, mul_comm, ← mul_assoc, mul_inv_cancel₀ hv0.ne', one_mul]
      exact hy
    · intro h1
      apply hψy
      have h2 := congrArg (fun z : ℂˣ => (z : ℂ)) h1
      simp only [standardCharacter_adjacentUnit_val, UnitaryAdditiveCharacter.complex_apply,
        Units.val_one] at h2
      exact Subtype.ext (by rw [h2, Circle.coe_one])
  exact UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone h.uniformizer
    (f := fun g => w.val.val (rankInclusion 1 g)) hf hK hθ hlam

/-- **Separation.** If every Laurent degree coefficient of the corank-one integral of a
restriction-invariant model vector `w` vanishes, then `w` vanishes on
`diag(GL_(n+1), 1)`. -/
theorem eq_zero_on_restriction_of_degreeCoefficients_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hzero : ∀ d, degreeCorankOneModelCoefficient h π hπ ℓ w d = 0)
    (g : Langlands.GeneralLinear (n + 1) F) :
    w.val.val (rankInclusion 1 g) = 0 := by
  obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent h.uniformizer g
  have heq' : g = (⟨u, hu⟩ : upperUnipotent (n + 1) F).val *
      torus ϖ (exponent h.uniformizer g) * k := heq
  have htorus : w.val.val (rankInclusion 1 (torus ϖ (exponent h.uniformizer g))) = 0 := by
    by_cases ha : Antitone (exponent h.uniformizer g)
    · exact torus_eq_zero_of_antitone_of_degreeCoefficients_eq_zero h π hπ ℓ w hw hzero ha
    · exact torus_eq_zero_of_not_antitone_of_restriction h π ℓ w hw ha
  rw [heq', hw _ ⟨k, hk⟩, map_mul]
  change w.val.val ((corankOneUnipotent ⟨u, hu⟩).val *
    rankInclusion 1 (torus ϖ (exponent h.uniformizer g))) = 0
  rw [w.val.property, htorus, mul_zero]

/-- The same separation, phrased through the Laurent series of the coefficients. -/
theorem eq_zero_on_restriction_of_corankOneModelLaurentSeries_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hL : corankOneModelLaurentSeries h π hπ ℓ w = 0)
    (g : Langlands.GeneralLinear (n + 1) F) :
    w.val.val (rankInclusion 1 g) = 0 :=
  eq_zero_on_restriction_of_degreeCoefficients_eq_zero h π hπ ℓ w hw
    (fun d => by rw [← corankOneModelLaurentSeries_coeff, hL, HahnSeries.coeff_zero]) g

end Model

end Langlands.Conductor
