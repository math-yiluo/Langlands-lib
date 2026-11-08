import Langlands.Representation.Conductor.SphericalSupport
import Langlands.Representation.Conductor.SphericalAnalysis
import Mathlib.Data.Int.Interval

/-! # Compact support of the actual Laurent degree integrands -/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa
open Langlands.Whittaker Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Matrix Topology

universe uF uV

variable {F : Type uF} [Field F]

private theorem rankInclusion_diagonalUnits {m : ℕ} (a : Fin m → Fˣ) :
    rankInclusion 1 (diagonalUnits a) =
      diagonalUnits (Fin.lastCases 1 a) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [diagonalUnits_val, Matrix.diagonal_apply]
  exact (Fin.castSucc_lt_last _).ne'

variable [ValuativeRel F] {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

include hϖ in
theorem uniformizer_zpow_mem_integer_iff (m : ℤ) :
    ((ϖ ^ m : Fˣ) : F) ∈ (ValuativeRel.valuation F).integer ↔ 0 ≤ m := by
  change ValuativeRel.valuation F ((ϖ ^ m : Fˣ) : F) ≤ 1 ↔ _
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_one_iff_right_of_lt_one₀
    (valuation_pos (ValuativeRel.valuation F) ϖ) hϖ.1

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ψ : UnitaryAdditiveCharacter F)
variable (ℓ : glFunctionals ψ (n + 1) π)

include hϖ hπ in
/-- A smooth model coefficient has a uniform lower bound on the last diagonal
exponent of its corank-one restriction, before choosing the integral factor. -/
theorem model_corankOne_last_exponent_lower_bound (hψ : HasIntegerConductor ψ)
    (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ b : ℤ, ∀ (lam : Fin (n + 1) → ℤ)
      (k : Langlands.GeneralLinear (n + 1) F),
      k ∈ integralSubgroup (ValuativeRel.valuation F).integer n →
      w.val.val (rankInclusion 1 (torus ϖ lam * k)) ≠ 0 →
      b ≤ lam (Fin.last n) := by
  obtain ⟨m, hm⟩ := model_diagonal_root_integral_bound hϖ π hπ ψ ℓ hψ w
  refine ⟨-m, fun lam k hk hw => ?_⟩
  let a : Fin ((n + 1) + 1) → Fˣ := Fin.lastCases 1 (fun i => ϖ ^ lam i)
  have hk' : rankInclusion 1 k ∈
      integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :=
    rankInclusion_mem (ValuativeRel.valuation F) hk
  have hw' : w.val.val (diagonalUnits a * rankInclusion 1 k) ≠ 0 := by
    simpa only [map_mul, torus, rankInclusion_diagonalUnits, a] using hw
  have hi := hm a (rankInclusion 1 k) hk' hw' (Fin.last n)
  simp only [a, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last,
    div_one] at hi
  have hp : ((ϖ ^ (lam (Fin.last n) + m) : Fˣ) : F) ∈
      (ValuativeRel.valuation F).integer := by
    simpa only [zpow_add, Units.val_mul] using hi
  have := (uniformizer_zpow_mem_integer_iff hϖ _).mp hp
  omega

variable (abv : AbsoluteValue F ℝ) (q : ℕ)

include hπ in
/-- At every nonzero value of the actual Laurent function all Iwasawa
exponents have a common lower bound. -/
theorem model_corankOne_polynomial_exponents_lower_bound (hψ : HasIntegerConductor ψ)
    (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ b : ℤ, ∀ g : Langlands.GeneralLinear (n + 1) F,
      corankOnePolynomialFunction ψ abv hϖ q w.val g ≠ 0 →
      ∀ i, b ≤ exponent hϖ g i := by
  obtain ⟨b, hb⟩ :=
    model_corankOne_last_exponent_lower_bound hϖ π hπ ψ ℓ hψ w
  refine ⟨b, fun g hg => ?_⟩
  have ha : Antitone (exponent hϖ g) := by
    by_contra hn
    apply hg
    simp [corankOnePolynomialFunction,
      sphericalWhittakerPolynomial_of_not_antitone hϖ
        (inverseStandardCharacter ψ n) q g hn]
  obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent hϖ g
  have heq' : g = (⟨u, hu⟩ : upperUnipotent (n + 1) F).val *
      (torus ϖ (exponent hϖ g) * k) := by
    simpa only [mul_assoc] using heq
  have hp : corankOnePolynomialFunction ψ abv hϖ q w.val
      (torus ϖ (exponent hϖ g) * k) ≠ 0 := by
    intro hp
    apply hg
    rw [heq', corankOnePolynomialFunction_invariant ψ abv hϖ q w.val hψ.1]
    exact hp
  have hw : w.val.val (rankInclusion 1 (torus ϖ (exponent hϖ g) * k)) ≠ 0 := by
    intro hw
    apply hp
    simp only [corankOnePolynomialFunction, hw, zero_mul, zero_smul]
  exact fun i => (hb _ k hk hw).trans (ha (Fin.le_last i))

/-- Integer exponent tuples bounded below and having one specified total degree. -/
def boundedDegreeExponents (m : ℕ) (b d : ℤ) : Set (Fin m → ℤ) :=
  {lam | (∀ i, b ≤ lam i) ∧ ∑ i, lam i = d}

theorem boundedDegreeExponents_finite (n : ℕ) (b d : ℤ) :
    (boundedDegreeExponents (n + 1) b d).Finite := by
  classical
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) =>
    Set.finite_Icc b (d - (n : ℤ) * b))).subset
  intro lam hlam i
  refine ⟨hlam.1 i, ?_⟩
  have hlo : (n : ℤ) * b ≤ ∑ j ∈ Finset.univ.erase i, lam j := by
    calc
      (n : ℤ) * b = ∑ _j ∈ Finset.univ.erase i, b := by simp
      _ ≤ ∑ j ∈ Finset.univ.erase i, lam j :=
        Finset.sum_le_sum (fun j _ => hlam.1 j)
  have hs := Finset.sum_erase_add Finset.univ lam (Finset.mem_univ i)
  rw [hlam.2] at hs
  omega

theorem boundedDegreeExponents_eq_empty_of_lt {m : ℕ} {b d : ℤ}
    (hd : d < (m : ℤ) * b) : boundedDegreeExponents m b d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro lam hlam
  have hs : (m : ℤ) * b ≤ ∑ i, lam i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlam.1 i))
  rw [hlam.2] at hs
  omega

/-- A finite collection of torus translates of the integral group, projected
to the actual left-unipotent quotient. -/
def boundedDegreeQuotientCarrier (ϖ : Fˣ) (b d : ℤ) :
    Set (LeftUnipotentQuotient n F) :=
  ⋃ lam ∈ boundedDegreeExponents (n + 1) b d,
    (fun k => leftQuotientMap (upperUnipotent (n + 1) F) (torus ϖ lam * k)) ''
      (integralSubgroup (ValuativeRel.valuation F).integer n :
        Set (Langlands.GeneralLinear (n + 1) F))

theorem boundedDegreeQuotientCarrier_isCompact (b d : ℤ) :
    IsCompact (boundedDegreeQuotientCarrier (n := n) ϖ b d) := by
  have hK : IsCompact (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) := by
    have hk := isCompact_levelOpenSubgroup F n 0
    change IsCompact (levelSubgroup F n 0 :
      Set (Langlands.GeneralLinear (n + 1) F)) at hk
    rwa [levelSubgroup_zero] at hk
  exact (boundedDegreeExponents_finite n b d).isCompact_biUnion (fun lam _ =>
    hK.image ((leftQuotient_isOpenQuotientMap
      (upperUnipotent (n + 1) F)).continuous.comp
        (continuous_const.mul continuous_id)))

include hπ in
/-- One bound gives an explicit compact carrier for every Laurent degree of
an actual smooth model vector. -/
theorem model_degreeCorankOnePolynomialIntegrand_support_subset
    (hψ : HasIntegerConductor ψ) (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ b : ℤ, ∀ d : ℤ,
      Function.support
        (degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ.1 d) ⊆
          boundedDegreeQuotientCarrier ϖ b d := by
  obtain ⟨b, hb⟩ :=
    model_corankOne_polynomial_exponents_lower_bound hϖ π hπ ψ ℓ abv q hψ w
  refine ⟨b, fun d t ht => ?_⟩
  induction t using Quotient.inductionOn with
  | h g =>
    change degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ.1 d
      (Quotient.mk _ g) ≠ 0 at ht
    have hd : sphericalQuotientDegree hϖ (Quotient.mk _ g) = d := by
      by_contra hn
      exact ht (ite_eq_right hn)
    have hp : corankOnePolynomialFunction ψ abv hϖ q w.val g ≠ 0 := by
      simpa only [degreeCorankOnePolynomialIntegrand, ite_eq_left hd,
        corankOnePolynomialIntegrand_mk] using ht
    have hlam : exponent hϖ g ∈ boundedDegreeExponents (n + 1) b d :=
      ⟨hb g hp, hd⟩
    obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent hϖ g
    refine Set.mem_iUnion.2 ⟨exponent hϖ g,
      Set.mem_iUnion.2 ⟨hlam, k, hk, ?_⟩⟩
    apply Quotient.sound
    change QuotientGroup.rightRel (upperUnipotent (n + 1) F)
      (torus ϖ (exponent hϖ g) * k) g
    rw [QuotientGroup.rightRel_apply]
    have heq' : g * (torus ϖ (exponent hϖ g) * k)⁻¹ = u := by
      calc
        _ = (u * (torus ϖ (exponent hϖ g) * k)) *
            (torus ϖ (exponent hϖ g) * k)⁻¹ :=
          congrArg (fun x => x * (torus ϖ (exponent hϖ g) * k)⁻¹)
            (heq.trans (mul_assoc _ _ _))
        _ = u := mul_inv_cancel_right _ _
    rw [heq']
    exact hu

include hπ in
/-- Every actual Laurent degree integrand of a smooth model vector has
compact support. -/
theorem model_degreeCorankOnePolynomialIntegrand_hasCompactSupport
    (hψ : HasIntegerConductor ψ) (w : (coefficientModel π ℓ).toSubmodule)
    (d : ℤ) :
    HasCompactSupport
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ.1 d) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : T2Space F := inferInstance
  let := leftQuotient_t2Space (upperUnipotent (n + 1) F) UpperUnipotent.isClosed
  obtain ⟨b, hb⟩ := model_degreeCorankOnePolynomialIntegrand_support_subset
    hϖ π hπ ψ ℓ abv q hψ w
  exact HasCompactSupport.of_support_subset_isCompact
    (boundedDegreeQuotientCarrier_isCompact b d) (hb d)

include hπ in
/-- The actual value span of every model degree integrand is finite. -/
theorem model_degreeCorankOnePolynomialSpan_finite
    (hψ : HasIntegerConductor ψ) (w : (coefficientModel π ℓ).toSubmodule)
    (d : ℤ) :
    Module.Finite ℂ (degreeCorankOnePolynomialSpan ψ abv hϖ q w.val hψ.1 d) := by
  obtain ⟨b, hb⟩ := model_degreeCorankOnePolynomialIntegrand_support_subset
    hϖ π hπ ψ ℓ abv q hψ w
  exact degreeCorankOnePolynomialSpan_finite_of_compactSupport ψ abv hϖ q w.val
    hψ.1 d (boundedDegreeQuotientCarrier_isCompact b d) (hb d)

include hπ in
/-- All sufficiently low Laurent degree integrands vanish identically. -/
theorem model_degreeCorankOnePolynomialIntegrand_eq_zero_below
    (hψ : HasIntegerConductor ψ) (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ d₀ : ℤ, ∀ d < d₀,
      degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ.1 d = 0 := by
  obtain ⟨b, hb⟩ := model_degreeCorankOnePolynomialIntegrand_support_subset
    hϖ π hπ ψ ℓ abv q hψ w
  refine ⟨(n + 1 : ℤ) * b, fun d hd => ?_⟩
  funext t
  by_contra ht
  have hs := hb d ht
  have he : boundedDegreeExponents (n + 1) b d = ∅ :=
    boundedDegreeExponents_eq_empty_of_lt (by exact_mod_cast hd)
  simp [boundedDegreeQuotientCarrier, he] at hs

section Normalized

open MeasureTheory

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)

include hπ in
/-- Compact support for the normalized actual degree integrand. -/
theorem degreeCorankOneModelIntegrand_hasCompactSupport
    (w : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    HasCompactSupport (degreeCorankOneModelIntegrand h π ℓ w d) :=
  model_degreeCorankOnePolynomialIntegrand_hasCompactSupport
    h.uniformizer π hπ ψ ℓ abv q h.conductor w d

include hπ in
/-- Scalar coefficient integrability of every normalized actual degree
integrand, with no compact-support premise. -/
theorem degreeCorankOneModelIntegrand_isScalarIntegrable
    (w : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    IsScalarIntegrable μ
      (coefficientSpanFunction (degreeCorankOneModelIntegrand h π ℓ w d)) :=
  degreeCorankOnePolynomialIntegrand_model_isScalarIntegrable h π hπ ℓ w d
    (degreeCorankOneModelIntegrand_hasCompactSupport π hπ ψ ℓ abv q h w d)

end Normalized

end Langlands.Conductor
