import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.Whittaker.DualTransform
import Langlands.Representation.Twist.Definitions

/-!
# JPSS zeta-value sets and normalized L-factors

The rational functions in `X = q^(-s)` obtained by continuing the actual JPSS integrals
of all Whittaker functions of a pair. The L-factor is the normalized polynomial generator
of their Laurent span, as a relation, with a constructor that needs its existence proof.
No convergence, rationality or existence theorem is assumed.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uV'

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']

section WhittakerSets

variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)

/-- All standard Whittaker functions of `π`: the coefficients `g ↦ ℓ (π g v)` of every
standard Whittaker functional `ℓ` and vector `v`. No functional is chosen. -/
def whittakerSet (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set (WhittakerFunctions ψ n) :=
  {W | ∃ ℓ : glFunctionals ψ n π, W ∈ (coefficientModel π ℓ).toSubmodule}

/-- All inverse-character Whittaker functions of `π`, for the second member of a pair. -/
def inverseWhittakerSet (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set (InverseWhittakerFunctions ψ n) :=
  {W | ∃ ℓ : glInverseFunctionals ψ n π, W ∈ (coefficientModel π ℓ).toSubmodule}

variable {ψ n}

theorem coefficientModel_subset_whittakerSet
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} (ℓ : glFunctionals ψ n π) :
    ((coefficientModel π ℓ).toSubmodule : Set (WhittakerFunctions ψ n)) ⊆
      whittakerSet ψ n π :=
  fun _ hW => ⟨ℓ, hW⟩

theorem coefficientModel_subset_inverseWhittakerSet
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (ℓ : glInverseFunctionals ψ n π) :
    ((coefficientModel π ℓ).toSubmodule : Set (InverseWhittakerFunctions ψ n)) ⊆
      inverseWhittakerSet ψ n π :=
  fun _ hW => ⟨ℓ, hW⟩

/-- The coefficients of a scalar multiple of a functional are coefficients of the
functional itself, so a one-dimensional functional space gives a single model. -/
theorem coefficientModel_smul_le {G : Type*} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
    {ρ : Representation ℂ G V} (ℓ : functionals N θ ρ) (c : ℂ) :
    (coefficientModel ρ (c • ℓ)).toSubmodule ≤ (coefficientModel ρ ℓ).toSubmodule := by
  rintro W ⟨v, rfl⟩
  refine ⟨c • v, ?_⟩
  ext g
  change ℓ.val (ρ g (c • v)) = c • ℓ.val (ρ g v)
  rw [map_smul, map_smul]

/-- If every standard functional is a multiple of `ℓ₀` (multiplicity one), the
intrinsic set is exactly the coefficient model of `ℓ₀`. -/
theorem whittakerSet_eq_coefficientModel
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} (ℓ₀ : glFunctionals ψ n π)
    (h : ∀ ℓ : glFunctionals ψ n π, ∃ c : ℂ, ℓ = c • ℓ₀) :
    whittakerSet ψ n π = (coefficientModel π ℓ₀).toSubmodule := by
  apply Set.Subset.antisymm
  · rintro W ⟨ℓ, hW⟩
    obtain ⟨c, rfl⟩ := h ℓ
    exact coefficientModel_smul_le ℓ₀ c hW
  · exact coefficientModel_subset_whittakerSet ℓ₀

/-- The inverse-character version of `whittakerSet_eq_coefficientModel`. -/
theorem inverseWhittakerSet_eq_coefficientModel
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (ℓ₀ : glInverseFunctionals ψ n π)
    (h : ∀ ℓ : glInverseFunctionals ψ n π, ∃ c : ℂ, ℓ = c • ℓ₀) :
    inverseWhittakerSet ψ n π = (coefficientModel π ℓ₀).toSubmodule := by
  apply Set.Subset.antisymm
  · rintro W ⟨ℓ, hW⟩
    obtain ⟨c, rfl⟩ := h ℓ
    exact coefficientModel_smul_le ℓ₀ c hW
  · exact coefficientModel_subset_inverseWhittakerSet ℓ₀

end WhittakerSets

section ZetaValues

variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Rational functions `R` such that, for some `W ∈ S`, `W' ∈ S'` and Schwartz--Bruhat `Φ`,
the equal-rank integral converges absolutely on a right half-plane and agrees there
with `R (q^(-s))`. -/
def equalRankValuesOf {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (S : Set (WhittakerFunctions ψ n)) (S' : Set (InverseWhittakerFunctions ψ n)) :
    Set RationalFunctions :=
  {R | ∃ W ∈ S, ∃ W' ∈ S', ∃ Φ : SchwartzBruhat (Fin (n + 1) → F),
    (∃ a : ℝ, ∀ s : ℂ, a < s.re → EqualRankConverges ψ abv μ W W' Φ s) ∧
      HasRationalContinuation q (equalRankIntegral ψ abv μ W W' Φ) R}

/-- The unequal-rank analogue for the block integral with fixed `j` and `k`. -/
def unequalRankValuesOf {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (S : Set (WhittakerFunctions ψ (n + (j + k + 1))))
    (S' : Set (InverseWhittakerFunctions ψ n)) : Set RationalFunctions :=
  {R | ∃ W ∈ S, ∃ W' ∈ S',
    (∃ a : ℝ, ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν W W' s) ∧
      HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ν W W') R}

theorem equalRankValuesOf_mono {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    {S T : Set (WhittakerFunctions ψ n)} {S' T' : Set (InverseWhittakerFunctions ψ n)}
    (h : S ⊆ T) (h' : S' ⊆ T') :
    equalRankValuesOf q ψ abv μ S S' ⊆ equalRankValuesOf q ψ abv μ T T' := by
  rintro R ⟨W, hW, W', hW', Φ, hc⟩
  exact ⟨W, h hW, W', h' hW', Φ, hc⟩

theorem unequalRankValuesOf_mono {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {S T : Set (WhittakerFunctions ψ (n + (j + k + 1)))}
    {S' T' : Set (InverseWhittakerFunctions ψ n)} (h : S ⊆ T) (h' : S' ⊆ T') :
    unequalRankValuesOf q ψ abv j k μ ν S S' ⊆ unequalRankValuesOf q ψ abv j k μ ν T T' := by
  rintro R ⟨W, hW, W', hW', hc⟩
  exact ⟨W, h hW, W', h' hW', hc⟩

/-- The equal-rank zeta values of the pair `(π, π')` (JPSS Theorem 2.7). -/
def equalRankZetaValues {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') : Set RationalFunctions :=
  equalRankValuesOf q ψ abv μ (whittakerSet ψ n π) (inverseWhittakerSet ψ n π')

/-- The unequal-rank zeta values `Ψ(s, W, W'; j)` of `(π, π')`, ranks
`n + (j + k + 1) + 1 > n + 1` (JPSS Theorem 2.7). -/
def unequalRankZetaValues {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') : Set RationalFunctions :=
  unequalRankValuesOf q ψ abv j k μ ν (whittakerSet ψ (n + (j + k + 1)) π)
    (inverseWhittakerSet ψ n π')

/-- Continuations of model integrals for specified functionals are zeta values. -/
theorem equalRankModel_mem_zetaValues {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n π')
    (W : (coefficientModel π ℓ).toSubmodule) (W' : (coefficientModel π' ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) {R : RationalFunctions}
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re → EqualRankConverges ψ abv μ W.val W'.val Φ s)
    (hR : HasRationalContinuation q
      (equalRankModelIntegral ψ abv μ π π' ℓ ℓ' W W' Φ) R) :
    R ∈ equalRankZetaValues q ψ abv μ π π' :=
  ⟨W.val, ⟨ℓ, W.property⟩, W'.val, ⟨ℓ', W'.property⟩, Φ, hconv, hR⟩

/-- Unequal-rank model integrals give unequal-rank zeta values. -/
theorem unequalRankModel_mem_zetaValues {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n π')
    (W : (coefficientModel π ℓ).toSubmodule) (W' : (coefficientModel π' ℓ').toSubmodule)
    {R : RationalFunctions}
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      UnequalRankConverges ψ abv j k μ ν W.val W'.val s)
    (hR : HasRationalContinuation q
      (unequalRankModelIntegral ψ abv j k μ ν π π' ℓ ℓ' W W') R) :
    R ∈ unequalRankZetaValues q ψ abv j k μ ν π π' :=
  ⟨W.val, ⟨ℓ, W.property⟩, W'.val, ⟨ℓ', W'.property⟩, hconv, hR⟩

/-- Under multiplicity one for both members, the zeta values are those of the
coefficient models of any spanning functionals. -/
theorem equalRankZetaValues_eq_model {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (ℓ₀ : glFunctionals ψ n π) (ℓ₀' : glInverseFunctionals ψ n π')
    (h : ∀ ℓ : glFunctionals ψ n π, ∃ c : ℂ, ℓ = c • ℓ₀)
    (h' : ∀ ℓ : glInverseFunctionals ψ n π', ∃ c : ℂ, ℓ = c • ℓ₀') :
    equalRankZetaValues q ψ abv μ π π' =
      equalRankValuesOf q ψ abv μ (coefficientModel π ℓ₀).toSubmodule
        (coefficientModel π' ℓ₀').toSubmodule := by
  rw [equalRankZetaValues, whittakerSet_eq_coefficientModel ℓ₀ h,
    inverseWhittakerSet_eq_coefficientModel ℓ₀' h']

theorem unequalRankZetaValues_eq_model {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (ℓ₀ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ₀' : glInverseFunctionals ψ n π')
    (h : ∀ ℓ : glFunctionals ψ (n + (j + k + 1)) π, ∃ c : ℂ, ℓ = c • ℓ₀)
    (h' : ∀ ℓ : glInverseFunctionals ψ n π', ∃ c : ℂ, ℓ = c • ℓ₀') :
    unequalRankZetaValues q ψ abv j k μ ν π π' =
      unequalRankValuesOf q ψ abv j k μ ν (coefficientModel π ℓ₀).toSubmodule
        (coefficientModel π' ℓ₀').toSubmodule := by
  rw [unequalRankZetaValues, whittakerSet_eq_coefficientModel ℓ₀ h,
    inverseWhittakerSet_eq_coefficientModel ℓ₀' h']

end ZetaValues

section LFactors

variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- `P` is the JPSS L-polynomial of an equal-rank pair: `P(0) = 1` and `1 / P(X)`
generates the Laurent span of the zeta values (JPSS Theorem 2.7(ii)). -/
def IsEqualRankLPolynomial {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) : Prop :=
  IsNormalizedGenerator (equalRankZetaValues q ψ abv μ π π') P

/-- The unequal-rank L-polynomial relation for the block integrals with fixed `j, k`. -/
def IsUnequalRankLPolynomial {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) : Prop :=
  IsNormalizedGenerator (unequalRankZetaValues q ψ abv j k μ ν π π') P

/-- The equal-rank L-factor `L(s, π × π') = 1 / P(q^(-s))` as a rational function of
`X = q^(-s)`, constructed only from a proof that the normalized generator exists. -/
def equalRankLFactor {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (h : NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π π')) :
    RationalFunctionsˣ :=
  normalizedFactor _ h

/-- The unequal-rank L-factor for fixed `j, k`, from its existence proof. -/
def unequalRankLFactor {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (h : NormalizedGeneratorExists (unequalRankZetaValues q ψ abv j k μ ν π π')) :
    RationalFunctionsˣ :=
  normalizedFactor _ h

theorem equalRankLFactor_eq {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (h : NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π π'))
    {P : ℂ[X]} (hP : IsEqualRankLPolynomial q ψ abv μ π π' P) :
    (equalRankLFactor q ψ abv μ π π' h : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [equalRankLFactor, coe_normalizedFactor, normalizedPolynomial_eq h hP]

theorem unequalRankLFactor_eq {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (h : NormalizedGeneratorExists (unequalRankZetaValues q ψ abv j k μ ν π π'))
    {P : ℂ[X]} (hP : IsUnequalRankLPolynomial q ψ abv j k μ ν π π' P) :
    (unequalRankLFactor q ψ abv j k μ ν π π' h : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [unequalRankLFactor, coe_normalizedFactor, normalizedPolynomial_eq h hP]

end LFactors

section NoFunctionals

/-! If a member of the pair has no nonzero functional and `1 < q`, the only zeta value is
`0` and no L-polynomial exists. For `q ≤ 1` the spectral point `q^(-s)` is degenerate:
at `q = 1` the nonzero `X - 1` continues the zero function. -/

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}

theorem whittakerSet_subset_zero {n : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (h : ∀ ℓ : glFunctionals ψ n π, ℓ = 0) : whittakerSet ψ n π ⊆ {0} := by
  rintro W ⟨ℓ, v, rfl⟩
  obtain rfl := h ℓ
  rw [Set.mem_singleton_iff]
  ext g
  rfl

theorem inverseWhittakerSet_subset_zero {n : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (h : ∀ ℓ : glInverseFunctionals ψ n π, ℓ = 0) : inverseWhittakerSet ψ n π ⊆ {0} := by
  rintro W ⟨ℓ, v, rfl⟩
  obtain rfl := h ℓ
  rw [Set.mem_singleton_iff]
  ext g
  rfl

/-- With `1 < q`, the zero function has no rational continuation other than `0`. -/
theorem eq_zero_of_hasRationalContinuation_zero (hq : 1 < q) {R : RationalFunctions}
    (h : HasRationalContinuation q (fun _ => 0) R) : R = 0 :=
  h.unique hq ⟨0, fun s _ => by simp⟩

/-- The hypothesis `1 < q` is needed: every spectral point is `1` when `q = 1`, so the
nonzero `X - 1` continues the zero function. -/
theorem exists_ne_zero_hasRationalContinuation_one :
    ∃ R : RationalFunctions, R ≠ 0 ∧ HasRationalContinuation 1 (fun _ => 0) R :=
  ⟨algebraMap ℂ[X] RationalFunctions (X - C 1),
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero 1), 0, fun s _ => by
      rw [spectralPoint, Nat.cast_one, Complex.one_cpow, RatFunc.denom_algebraMap,
        RatFunc.eval_algebraMap]
      simp⟩

theorem equalRankIntegral_eq_zero {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) {W : WhittakerFunctions ψ n}
    {W' : InverseWhittakerFunctions ψ n} (h : W = 0 ∨ W' = 0)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankIntegral ψ abv μ W W' Φ = fun _ => 0 := by
  funext s
  have hzero : ∀ y, equalRankIntegrand ψ abv W W' Φ s y = 0 := by
    intro y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    rcases h with rfl | rfl <;> simp [equalRankIntegrand_mk]
  simp [equalRankIntegral, hzero]

theorem unequalRankIntegral_eq_zero {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {W : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    (h : W = 0 ∨ W' = 0) :
    unequalRankIntegral ψ abv j k μ ν W W' = fun _ => 0 := by
  funext s
  have hzero : ∀ x y, unequalRankIntegrand ψ abv j k W W' s x y = 0 := by
    intro x y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    rcases h with rfl | rfl <;> simp [unequalRankIntegrand_mk]
  simp [unequalRankIntegral, hzero]

theorem equalRankValuesOf_subset_zero (hq : 1 < q) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    {S : Set (WhittakerFunctions ψ n)} {S' : Set (InverseWhittakerFunctions ψ n)}
    (h : S ⊆ {0} ∨ S' ⊆ {0}) : equalRankValuesOf q ψ abv μ S S' ⊆ {0} := by
  rintro R ⟨W, hW, W', hW', Φ, -, hR⟩
  rw [equalRankIntegral_eq_zero μ (h.imp (fun h => h hW) (fun h => h hW')) Φ] at hR
  exact eq_zero_of_hasRationalContinuation_zero hq hR

theorem unequalRankValuesOf_subset_zero (hq : 1 < q) {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {S : Set (WhittakerFunctions ψ (n + (j + k + 1)))}
    {S' : Set (InverseWhittakerFunctions ψ n)} (h : S ⊆ {0} ∨ S' ⊆ {0}) :
    unequalRankValuesOf q ψ abv j k μ ν S S' ⊆ {0} := by
  rintro R ⟨W, hW, W', hW', -, hR⟩
  rw [unequalRankIntegral_eq_zero j k μ ν (h.imp (fun h => h hW) (fun h => h hW'))] at hR
  exact eq_zero_of_hasRationalContinuation_zero hq hR

/-- If `π` or `π'` has no nonzero functional and `1 < q`, every zeta value is `0`. -/
theorem equalRankZetaValues_subset_zero (hq : 1 < q) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (h : (∀ ℓ : glFunctionals ψ n π, ℓ = 0) ∨ ∀ ℓ' : glInverseFunctionals ψ n π', ℓ' = 0) :
    equalRankZetaValues q ψ abv μ π π' ⊆ {0} :=
  equalRankValuesOf_subset_zero hq μ
    (h.imp whittakerSet_subset_zero inverseWhittakerSet_subset_zero)

theorem unequalRankZetaValues_subset_zero (hq : 1 < q) {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (h : (∀ ℓ : glFunctionals ψ (n + (j + k + 1)) π, ℓ = 0) ∨
      ∀ ℓ' : glInverseFunctionals ψ n π', ℓ' = 0) :
    unequalRankZetaValues q ψ abv j k μ ν π π' ⊆ {0} :=
  unequalRankValuesOf_subset_zero hq j k μ ν
    (h.imp whittakerSet_subset_zero inverseWhittakerSet_subset_zero)

/-- Values contained in `{0}` span the zero module, which has no normalized generator. -/
theorem not_isNormalizedGenerator_of_subset_zero {values : Set RationalFunctions}
    (h : values ⊆ {0}) (P : ℂ[X]) : ¬ IsNormalizedGenerator values P := by
  intro hP
  have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [hP.2]
    exact Submodule.mem_span_singleton_self _
  have hbot : zetaSpan values = ⊥ := by
    rw [zetaSpan, Submodule.span_eq_bot]
    exact fun x hx => h hx
  rw [hbot, Submodule.mem_bot, inv_eq_zero] at hmem
  exact RatFunc.algebraMap_ne_zero hP.polynomial_ne_zero hmem

theorem not_normalizedGeneratorExists_of_subset_zero {values : Set RationalFunctions}
    (h : values ⊆ {0}) : ¬ NormalizedGeneratorExists values :=
  fun ⟨P, hP⟩ => not_isNormalizedGenerator_of_subset_zero h P hP

/-- With `1 < q`, a pair one of whose members has no nonzero functional has no
equal-rank L-polynomial, so no equal-rank L-factor can be constructed. -/
theorem not_normalizedGeneratorExists_equalRank (hq : 1 < q) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (h : (∀ ℓ : glFunctionals ψ n π, ℓ = 0) ∨ ∀ ℓ' : glInverseFunctionals ψ n π', ℓ' = 0) :
    ¬ NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π π') :=
  not_normalizedGeneratorExists_of_subset_zero (equalRankZetaValues_subset_zero hq μ h)

/-- The unequal-rank analogue of `not_normalizedGeneratorExists_equalRank`. -/
theorem not_normalizedGeneratorExists_unequalRank (hq : 1 < q) {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    (h : (∀ ℓ : glFunctionals ψ (n + (j + k + 1)) π, ℓ = 0) ∨
      ∀ ℓ' : glInverseFunctionals ψ n π', ℓ' = 0) :
    ¬ NormalizedGeneratorExists (unequalRankZetaValues q ψ abv j k μ ν π π') :=
  not_normalizedGeneratorExists_of_subset_zero (unequalRankZetaValues_subset_zero hq j k μ ν h)

end NoFunctionals

section CharacterPairs

variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- The one-dimensional representation `χ ∘ det` of `GL_1`, from the published
character representation. -/
abbrev rankOneCharacter (χ : Fˣ →* ℂˣ) : Representation ℂ (Langlands.GeneralLinear 1 F) ℂ :=
  Langlands.characterRepresentation (χ.comp determinant)

/-- The identity relabelling of coordinates identifying the rank in which the
unequal-rank family writes `GL_(m+2)` with `GL_(m+2)` itself. -/
def characterPairRank (m : ℕ) :
    Langlands.GeneralLinear (0 + (0 + m + 1) + 1) F ≃* Langlands.GeneralLinear (m + 1 + 1) F :=
  GeneralLinear.reindex (finCongr (by omega))

/-- Zeta values of `π × χ` for `π` on `GL_(m+1)` and a character `χ` of `GL_1`:
the equal-rank family when `m = 0`, otherwise the block family with `j = 0`,
whose zero-dimensional rectangular variable carries the unit point mass. -/
def characterZetaValues [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (χ : Fˣ →* ℂˣ) :
    (m : ℕ) → Representation ℂ (Langlands.GeneralLinear (m + 1) F) V → Set RationalFunctions
  | 0, π => equalRankZetaValues q ψ abv μ π (rankOneCharacter χ)
  | m + 1, π =>
    letI : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) := ⊤
    unequalRankZetaValues q ψ abv 0 m μ (Measure.dirac 0)
      (π.comp (characterPairRank m).toMonoidHom) (rankOneCharacter χ)

/-- `P` is the L-polynomial of `π × χ`; with `χ = 1` this is the standard `L(s, π)`. -/
def IsCharacterLPolynomial [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (χ : Fˣ →* ℂˣ) {m : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V) (P : ℂ[X]) : Prop :=
  IsNormalizedGenerator (characterZetaValues q ψ abv μ χ m π) P

/-- `L(s, π × χ)`, from a proof that its normalized generator exists. -/
def characterLFactor [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (χ : Fˣ →* ℂˣ) {m : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (h : NormalizedGeneratorExists (characterZetaValues q ψ abv μ χ m π)) :
    RationalFunctionsˣ :=
  normalizedFactor _ h

/-- The standard L-factor `L(s, π) = L(s, π × 1)`. -/
abbrev standardLFactor [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) {m : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (h : NormalizedGeneratorExists (characterZetaValues q ψ abv μ 1 m π)) :
    RationalFunctionsˣ :=
  characterLFactor q ψ abv μ 1 π h

end CharacterPairs

section MeasureScaling

open scoped ENNReal

/-- Multiplying a function of `s` by a constant multiplies its rational continuation. -/
theorem hasRationalContinuation_const_mul {q : ℕ} {f : ℂ → ℂ} {R : RationalFunctions}
    (c : ℂ) (h : HasRationalContinuation q f R) :
    HasRationalContinuation q (fun s => c * f s) (RatFunc.C c * R) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun s hs => ?_⟩
  obtain ⟨hd, he⟩ := ha s hs
  have hC : Polynomial.eval₂ (RingHom.id ℂ) (spectralPoint q s) (RatFunc.C c).denom ≠ 0 := by
    simp [RatFunc.denom_C]
  have hR : Polynomial.eval₂ (RingHom.id ℂ) (spectralPoint q s) R.denom ≠ 0 := hd
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ)
      (spectralPoint q s) (RatFunc.denom_mul_dvd (RatFunc.C c) R) h0
    rw [Polynomial.eval₂_mul] at h1
    exact mul_ne_zero hC hR h1
  · rw [RatFunc.eval_mul (RingHom.id ℂ) (spectralPoint q s) hC hR, RatFunc.eval_C, ← he]
    rfl

/-- The Laurent embedding sends constants to constants. -/
theorem laurentToRatFunc_C (c : ℂ) : laurentToRatFunc (LaurentPolynomial.C c) = RatFunc.C c :=
  LaurentPolynomial.eval₂_C _ _ c

/-- Two value sets that are nonzero constant multiples of each other have the same
Laurent span. -/
theorem zetaSpan_eq_of_const_mul {S T : Set RationalFunctions} {c : ℂ} (hc : c ≠ 0)
    (hST : ∀ R ∈ S, RatFunc.C c * R ∈ T) (hTS : ∀ R ∈ T, RatFunc.C c⁻¹ * R ∈ S) :
    zetaSpan S = zetaSpan T := by
  have key : ∀ {A B : Set RationalFunctions} {a : ℂ}, a ≠ 0 →
      (∀ R ∈ A, RatFunc.C a * R ∈ B) → zetaSpan A ≤ zetaSpan B := by
    intro A B a ha hAB
    refine Submodule.span_le.2 fun R hR => ?_
    have hmem : LaurentPolynomial.C a⁻¹ • (RatFunc.C a * R) ∈ zetaSpan B :=
      Submodule.smul_mem _ _ (mem_zetaSpan (hAB R hR))
    rwa [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ ha, map_one, one_mul] at hmem
  exact le_antisymm (key hc hST) (key (inv_ne_zero hc) hTS)

/-- The normalized-generator relation depends only on the Laurent span. -/
theorem isNormalizedGenerator_congr {S T : Set RationalFunctions}
    (h : zetaSpan S = zetaSpan T) (P : ℂ[X]) :
    IsNormalizedGenerator S P ↔ IsNormalizedGenerator T P := by
  rw [IsNormalizedGenerator, IsNormalizedGenerator, h]

/-- Value sets with the same Laurent span have the same normalized-generator existence. -/
theorem normalizedGeneratorExists_congr {S T : Set RationalFunctions}
    (h : zetaSpan S = zetaSpan T) :
    NormalizedGeneratorExists S ↔ NormalizedGeneratorExists T := by
  simp only [NormalizedGeneratorExists, isNormalizedGenerator_congr h]

variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Rescaling the quotient measure by a finite nonzero constant does not change the
Laurent span of the equal-rank values. -/
theorem zetaSpan_equalRankValuesOf_smul_measure {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (S : Set (WhittakerFunctions ψ n)) (S' : Set (InverseWhittakerFunctions ψ n)) :
    zetaSpan (equalRankValuesOf q ψ abv (c • μ) S S') =
      zetaSpan (equalRankValuesOf q ψ abv μ S S') := by
  have hr : ((c.toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc₀, hc⟩)
  have hconv : ∀ W W' Φ s, EqualRankConverges ψ abv (c • μ) W W' Φ s ↔
      EqualRankConverges ψ abv μ W W' Φ s := fun _ _ _ _ =>
    integrable_smul_measure hc₀ hc
  have hint : ∀ W W' Φ, equalRankIntegral ψ abv (c • μ) W W' Φ =
      fun s => ((c.toReal : ℝ) : ℂ) * equalRankIntegral ψ abv μ W W' Φ s := by
    intro W W' Φ
    funext s
    rw [equalRankIntegral, integral_smul_measure, Complex.real_smul]
    rfl
  refine zetaSpan_eq_of_const_mul (inv_ne_zero hr) ?_ ?_
  · rintro R ⟨W, hW, W', hW', Φ, ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', Φ, ⟨a, fun s hs => (hconv W W' Φ s).1 (ha s hs)⟩, ?_⟩
    have h := hasRationalContinuation_const_mul ((c.toReal : ℝ) : ℂ)⁻¹ hR
    convert h using 1
    funext s
    rw [hint]
    exact (inv_mul_cancel_left₀ hr _).symm
  · rintro R ⟨W, hW, W', hW', Φ, ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', Φ, ⟨a, fun s hs => (hconv W W' Φ s).2 (ha s hs)⟩, ?_⟩
    rw [inv_inv, hint]
    exact hasRationalContinuation_const_mul _ hR

/-- Rescaling the quotient measure does not change the Laurent span of the
unequal-rank values. -/
theorem zetaSpan_unequalRankValuesOf_smul_measure {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    [SFinite ν] {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (S : Set (WhittakerFunctions ψ (n + (j + k + 1))))
    (S' : Set (InverseWhittakerFunctions ψ n)) :
    zetaSpan (unequalRankValuesOf q ψ abv j k (c • μ) ν S S') =
      zetaSpan (unequalRankValuesOf q ψ abv j k μ ν S S') := by
  have hr : ((c.toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc₀, hc⟩)
  have hconv : ∀ W W' s, UnequalRankConverges ψ abv j k (c • μ) ν W W' s ↔
      UnequalRankConverges ψ abv j k μ ν W W' s := by
    intro W W' s
    rw [UnequalRankConverges, UnequalRankConverges, Measure.prod_smul_left]
    exact integrable_smul_measure hc₀ hc
  have hint : ∀ W W', unequalRankIntegral ψ abv j k (c • μ) ν W W' =
      fun s => ((c.toReal : ℝ) : ℂ) * unequalRankIntegral ψ abv j k μ ν W W' s := by
    intro W W'
    funext s
    rw [unequalRankIntegral, integral_smul_measure, Complex.real_smul]
    rfl
  refine zetaSpan_eq_of_const_mul (inv_ne_zero hr) ?_ ?_
  · rintro R ⟨W, hW, W', hW', ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', ⟨a, fun s hs => (hconv W W' s).1 (ha s hs)⟩, ?_⟩
    have h := hasRationalContinuation_const_mul ((c.toReal : ℝ) : ℂ)⁻¹ hR
    convert h using 1
    funext s
    rw [hint]
    exact (inv_mul_cancel_left₀ hr _).symm
  · rintro R ⟨W, hW, W', hW', ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', ⟨a, fun s hs => (hconv W W' s).2 (ha s hs)⟩, ?_⟩
    rw [inv_inv, hint]
    exact hasRationalContinuation_const_mul _ hR

/-- The equal-rank L-polynomial does not depend on the normalization of `μ`. -/
theorem isEqualRankLPolynomial_smul_measure {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) :
    IsEqualRankLPolynomial q ψ abv (c • μ) π π' P ↔
      IsEqualRankLPolynomial q ψ abv μ π π' P :=
  isNormalizedGenerator_congr
    (zetaSpan_equalRankValuesOf_smul_measure q ψ abv μ hc₀ hc _ _) P

/-- The unequal-rank L-polynomial does not depend on the normalization of `μ`. -/
theorem isUnequalRankLPolynomial_smul_measure {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    [SFinite ν] {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k (c • μ) ν π π' P ↔
      IsUnequalRankLPolynomial q ψ abv j k μ ν π π' P :=
  isNormalizedGenerator_congr
    (zetaSpan_unequalRankValuesOf_smul_measure q ψ abv j k μ ν hc₀ hc _ _) P

/-- The L-polynomial of `π × χ`, in particular the standard one, does not depend on
the normalization of the measure on `GL_1`. -/
theorem isCharacterLPolynomial_smul_measure [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (χ : Fˣ →* ℂˣ) {m : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (P : ℂ[X]) :
    IsCharacterLPolynomial q ψ abv (c • μ) χ π P ↔ IsCharacterLPolynomial q ψ abv μ χ π P := by
  cases m with
  | zero => exact isEqualRankLPolynomial_smul_measure q ψ abv μ hc₀ hc π _ P
  | succ m =>
    let : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) := ⊤
    exact isUnequalRankLPolynomial_smul_measure q ψ abv 0 m μ (Measure.dirac 0) hc₀ hc _ _ P

end MeasureScaling

section DualPairs

variable [IsTopologicalRing F]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Zeta values of the pair `(π^ι, π'^ι)` of inverse-transpose pullbacks with respect
to `ψ⁻¹ = ψ.scale (-1)`, the pair on the left of the JPSS functional equation. -/
def dualEqualRankZetaValues {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') : Set RationalFunctions :=
  equalRankZetaValues q (ψ.scale (-1)) abv μ (inverseTransposePullback π)
    (inverseTransposePullback π')

/-- The unequal-rank dual-pair zeta values, with the same `j, k`. -/
def dualUnequalRankZetaValues {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') : Set RationalFunctions :=
  unequalRankZetaValues q (ψ.scale (-1)) abv j k μ ν (inverseTransposePullback π)
    (inverseTransposePullback π')

variable {q abv}

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- Equivariant functionals for equal characters, with the same underlying functional. -/
def functionalsCongr {G : Type*} [Group G] {N : Subgroup G} {θ θ' : N →* ℂˣ}
    {ρ : Representation ℂ G V} (h : θ = θ') (ℓ : functionals N θ ρ) :
    functionals N θ' ρ :=
  ⟨ℓ.val, h ▸ ℓ.property⟩

/-- The transform `W ↦ (g ↦ W(w_n (g^(-1))^T))` maps the Whittaker functions of `π`
into the Whittaker functions of `π^ι` for the base character `ψ.scale (-1)`. -/
theorem dualFunction_mem_whittakerSet {n : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} {W : WhittakerFunctions ψ n}
    (hW : W ∈ whittakerSet ψ n π) :
    ∃ W' ∈ whittakerSet (ψ.scale (-1)) n (inverseTransposePullback π),
      W'.val = dualFunction n W.val := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  have hχ : standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n := by
    rw [← scaledStandardCharacter_neg_one]
    ext u
    rfl
  let ℓ' : glFunctionals (ψ.scale (-1)) n (inverseTransposePullback π) :=
    functionalsCongr hχ.symm (dualFunctional ψ π ℓ)
  refine ⟨coefficientMap (inverseTransposePullback π) ℓ' v, ⟨ℓ', v, rfl⟩, ?_⟩
  exact (dualFunction_coefficient ψ π ℓ v).symm

/-- The same transform maps inverse-character Whittaker functions of `π'` into the
inverse-character Whittaker functions of `π'^ι` for `ψ.scale (-1)`. -/
theorem dualFunction_mem_inverseWhittakerSet {n : ℕ}
    {π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V'}
    {W : InverseWhittakerFunctions ψ n} (hW : W ∈ inverseWhittakerSet ψ n π') :
    ∃ W' ∈ inverseWhittakerSet (ψ.scale (-1)) n (inverseTransposePullback π'),
      W'.val = dualFunction n W.val := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  have hχ : standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n := by
    rw [← scaledStandardCharacter_neg_one]
    ext u
    rfl
  let ℓ₁ : glFunctionals (ψ.scale (-1)) n π' := functionalsCongr hχ.symm ℓ
  let ℓ' : glInverseFunctionals (ψ.scale (-1)) n (inverseTransposePullback π') :=
    dualFunctional (ψ.scale (-1)) π' ℓ₁
  refine ⟨coefficientMap (inverseTransposePullback π') ℓ' v, ⟨ℓ', v, rfl⟩, ?_⟩
  exact (dualFunction_coefficient (ψ.scale (-1)) π' ℓ₁ v).symm

end DualPairs

end Langlands.RankinSelberg
