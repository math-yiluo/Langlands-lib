import Langlands.Representation.RankinSelberg.AnalyticBridge
import Langlands.Representation.RankinSelberg.TwistInvariance

/-!
# The L-factor of a pair

For `π` on `GL_(r+1)` and `σ` on `GL_(n+1)` with `n ≤ r`, the L-polynomial of the pair
is the normalized generator of the equal-rank zeta values when `r = n`, and the common
normalized generator of the zeta values of every rectangular block when `n < r`
(JPSS Theorem 2.7(ii)). The L-factor is constructed only from a proof that this
polynomial exists. The relation is invariant under equivalences and determinant
twists, the dual pair uses the inverse-transpose pullbacks and `ψ⁻¹`, and the p-adic
analytic statements supply the existence proof for pairs of Whittaker type.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial QuotientIntegration
open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF uV uW uV₂ uW₂

section Surjections

variable {G : Type*} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {ρ : Representation ℂ G V} {ρ₂ : Representation ℂ G V₂}

/-- Along a surjective intertwining map `ρ → ρ₂`, every coefficient of `ρ₂` is a
coefficient of `ρ`: compose the functional with the map. -/
theorem exists_coefficientMap_eq_of_surjective (f : ρ.IntertwiningMap ρ₂)
    (hf : Function.Surjective f) (ℓ₂ : functionals N θ ρ₂) (v₂ : V₂) :
    ∃ (ℓ : functionals N θ ρ) (v : V), coefficientMap ρ ℓ v = coefficientMap ρ₂ ℓ₂ v₂ := by
  obtain ⟨v, rfl⟩ := hf v₂
  refine ⟨⟨ℓ₂.val ∘ₗ f.toLinearMap, fun m w => ?_⟩, v, ?_⟩
  · change ℓ₂.val (f (ρ (m : G) w)) = (θ m : ℂ) * ℓ₂.val (f w)
    rw [f.isIntertwining]
    exact ℓ₂.property m (f w)
  · apply Subtype.ext
    funext g
    change ℓ₂.val (f (ρ g v)) = ℓ₂.val (ρ₂ g (f v))
    rw [f.isIntertwining]

end Surjections

section WhittakerSets

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}

/-- The Whittaker functions of a quotient are Whittaker functions of the source. -/
theorem whittakerSet_subset_of_surjective (f : π.IntertwiningMap π₂)
    (hf : Function.Surjective f) : whittakerSet ψ n π₂ ⊆ whittakerSet ψ n π := by
  rintro W ⟨ℓ₂, v₂, rfl⟩
  obtain ⟨ℓ, v, h⟩ := exists_coefficientMap_eq_of_surjective f hf ℓ₂ v₂
  exact ⟨ℓ, v, h⟩

/-- The inverse-character analogue of `whittakerSet_subset_of_surjective`. -/
theorem inverseWhittakerSet_subset_of_surjective (f : π.IntertwiningMap π₂)
    (hf : Function.Surjective f) : inverseWhittakerSet ψ n π₂ ⊆ inverseWhittakerSet ψ n π := by
  rintro W ⟨ℓ₂, v₂, rfl⟩
  obtain ⟨ℓ, v, h⟩ := exists_coefficientMap_eq_of_surjective f hf ℓ₂ v₂
  exact ⟨ℓ, v, h⟩

/-- Equivalent representations have the same Whittaker functions. -/
theorem whittakerSet_eq_of_equiv (φ : π.Equiv π₂) : whittakerSet ψ n π = whittakerSet ψ n π₂ :=
  Set.Subset.antisymm
    (whittakerSet_subset_of_surjective ψ φ.symm.toIntertwiningMap (EquivLike.surjective φ.symm))
    (whittakerSet_subset_of_surjective ψ φ.toIntertwiningMap (EquivLike.surjective φ))

/-- Equivalent representations have the same inverse-character Whittaker functions. -/
theorem inverseWhittakerSet_eq_of_equiv (φ : π.Equiv π₂) :
    inverseWhittakerSet ψ n π = inverseWhittakerSet ψ n π₂ :=
  Set.Subset.antisymm
    (inverseWhittakerSet_subset_of_surjective ψ φ.symm.toIntertwiningMap
      (EquivLike.surjective φ.symm))
    (inverseWhittakerSet_subset_of_surjective ψ φ.toIntertwiningMap (EquivLike.surjective φ))

end WhittakerSets

section ZetaValueTransport

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- Zeta values of a pair of quotients are zeta values of the pair. -/
theorem equalRankZetaValues_subset_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (f' : σ.IntertwiningMap σ₂) (hf' : Function.Surjective f') :
    equalRankZetaValues q ψ abv μ π₂ σ₂ ⊆ equalRankZetaValues q ψ abv μ π σ :=
  equalRankValuesOf_mono q ψ abv μ (whittakerSet_subset_of_surjective ψ f hf)
    (inverseWhittakerSet_subset_of_surjective ψ f' hf')

/-- Equivalent pairs have the same equal-rank zeta values. -/
theorem equalRankZetaValues_eq_of_equiv
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    equalRankZetaValues q ψ abv μ π σ = equalRankZetaValues q ψ abv μ π₂ σ₂ := by
  rw [equalRankZetaValues, equalRankZetaValues, whittakerSet_eq_of_equiv ψ φ,
    inverseWhittakerSet_eq_of_equiv ψ φ']

variable (j k : ℕ) [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))

/-- The unequal-rank analogue of `equalRankZetaValues_subset_of_surjective`. -/
theorem unequalRankZetaValues_subset_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (f' : σ.IntertwiningMap σ₂) (hf' : Function.Surjective f') :
    unequalRankZetaValues q ψ abv j k μ ν π₂ σ₂ ⊆ unequalRankZetaValues q ψ abv j k μ ν π σ :=
  unequalRankValuesOf_mono q ψ abv j k μ ν (whittakerSet_subset_of_surjective ψ f hf)
    (inverseWhittakerSet_subset_of_surjective ψ f' hf')

/-- Equivalent pairs have the same unequal-rank zeta values. -/
theorem unequalRankZetaValues_eq_of_equiv
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    unequalRankZetaValues q ψ abv j k μ ν π σ = unequalRankZetaValues q ψ abv j k μ ν π₂ σ₂ := by
  rw [unequalRankZetaValues, unequalRankZetaValues, whittakerSet_eq_of_equiv ψ φ,
    inverseWhittakerSet_eq_of_equiv ψ φ']

end ZetaValueTransport

section FixedRanks

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The unequal-rank zeta values of the block `j, k` with the large rank `r` fixed
independently of the block. The rank equation transports only types. -/
def unequalRankZetaValuesAt (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) : Set RationalFunctions := by
  subst r
  exact unequalRankZetaValues q ψ abv j k μ ν π σ

variable (j k : ℕ) [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- At the defining rank the transported values are the block zeta values. -/
theorem unequalRankZetaValuesAt_rfl
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V) :
    unequalRankZetaValuesAt j k rfl q ψ abv μ ν π σ = unequalRankZetaValues q ψ abv j k μ ν π σ :=
  rfl

/-- Determinant twists of the two members by `χ` and `χ⁻¹` do not change the
transported block zeta values. -/
theorem unequalRankZetaValuesAt_twist (hr : r = n + (j + k + 1)) (χ : Fˣ →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V) :
    unequalRankZetaValuesAt j k hr q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) σ) =
      unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ := by
  subst hr
  exact unequalRankZetaValues_twist q ψ abv χ j k μ ν π σ

/-- Equivalent pairs have the same transported block zeta values. -/
theorem unequalRankZetaValuesAt_eq_of_equiv (hr : r = n + (j + k + 1))
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ =
      unequalRankZetaValuesAt j k hr q ψ abv μ ν π₂ σ₂ := by
  subst hr
  exact unequalRankZetaValues_eq_of_equiv q ψ abv μ j k ν φ φ'

end FixedRanks

section PairRelation

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- `P` is the L-polynomial of the pair `(π, σ)`, `π` on `GL_(r+1)`, `σ` on `GL_(n+1)`.
When `n < r` it is the common normalized generator of the zeta values of every block
`r = n + (j + k + 1)`, with the rectangular product of `ν` on the `j × (n+1)` variable;
when `r = n` it is the equal-rank L-polynomial; there is none when `r < n`. -/
def IsPairLPolynomial (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) : Prop :=
  if n < r then
    ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankZetaValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1)) π σ) P
  else if hrn : r = n then IsEqualRankLPolynomial (n := n) q ψ abv μ (hrn ▸ π) σ P
  else False

/-- The L-polynomial of the pair exists. -/
def PairLPolynomialExists (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) : Prop :=
  ∃ P : ℂ[X], IsPairLPolynomial q ψ abv μ ν π σ P

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {P P' : ℂ[X]}

theorem isPairLPolynomial_of_lt (hnr : n < r) :
    IsPairLPolynomial q ψ abv μ ν π σ P ↔
      ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
        IsNormalizedGenerator
          (unequalRankZetaValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1)) π σ) P := by
  rw [IsPairLPolynomial, ite_eq_left hnr]

theorem isPairLPolynomial_self {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} :
    IsPairLPolynomial q ψ abv μ ν π σ P ↔ IsEqualRankLPolynomial q ψ abv μ π σ P := by
  rw [IsPairLPolynomial, ite_eq_right (lt_irrefl n), dite_eq_left rfl]

/-- There is no L-polynomial when the second rank exceeds the first. -/
theorem not_isPairLPolynomial_of_lt (hrn : r < n) : ¬ IsPairLPolynomial q ψ abv μ ν π σ P := by
  rw [IsPairLPolynomial, ite_eq_right (by omega), dite_eq_right (by omega)]
  exact id

/-- For `π` on `GL_(n+(j+k+1)+1)` the pair L-polynomial is the L-polynomial of the
block `j, k`. -/
theorem IsPairLPolynomial.isUnequalRankLPolynomial (j k : ℕ)
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    (h : IsPairLPolynomial q ψ abv μ ν π σ P) :
    IsUnequalRankLPolynomial q ψ abv j k μ (rectangularMeasure ν j (n + 1)) π σ P :=
  (isPairLPolynomial_of_lt (by omega)).1 h j k rfl

/-- In unequal rank, one block family with a normalized generator determines it. -/
theorem IsPairLPolynomial.unique (h : IsPairLPolynomial q ψ abv μ ν π σ P)
    (h' : IsPairLPolynomial q ψ abv μ ν π σ P') : P = P' := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr] at h h'
    have hr : r = n + (0 + (r - n - 1) + 1) := by omega
    exact (h 0 (r - n - 1) hr).unique (h' 0 (r - n - 1) hr)
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self] at h h'
      exact IsNormalizedGenerator.unique h h'
    · exact absurd h (not_isPairLPolynomial_of_lt (by omega))

theorem IsPairLPolynomial.coeff_zero (h : IsPairLPolynomial q ψ abv μ ν π σ P) :
    P.coeff 0 = 1 := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr] at h
    exact (h 0 (r - n - 1) (by omega)).1
  · by_cases hrn : r = n
    · subst hrn
      exact (isPairLPolynomial_self.1 h).1
    · exact absurd h (not_isPairLPolynomial_of_lt (by omega))

theorem IsPairLPolynomial.ne_zero (h : IsPairLPolynomial q ψ abv μ ν π σ P) : P ≠ 0 := by
  rintro rfl
  simpa using h.coeff_zero

/-- Only a proof of existence selects the L-polynomial. -/
def pairLPolynomial (h : PairLPolynomialExists q ψ abv μ ν π σ) : ℂ[X] :=
  h.choose

theorem pairLPolynomial_spec (h : PairLPolynomialExists q ψ abv μ ν π σ) :
    IsPairLPolynomial q ψ abv μ ν π σ (pairLPolynomial h) :=
  h.choose_spec

theorem pairLPolynomial_eq (h : PairLPolynomialExists q ψ abv μ ν π σ)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P) : pairLPolynomial h = P :=
  (pairLPolynomial_spec h).unique hP

/-- The L-factor `L(s, π × σ) = 1 / P(q^(-s))` of the pair, as a unit rational function
of `X = q^(-s)`, constructed from a proof that its L-polynomial exists. -/
def pairLFactor (h : PairLPolynomialExists q ψ abv μ ν π σ) : RationalFunctionsˣ :=
  (Units.mk0 (algebraMap ℂ[X] RationalFunctions (pairLPolynomial h))
    (RatFunc.algebraMap_ne_zero (pairLPolynomial_spec h).ne_zero))⁻¹

@[simp]
theorem coe_pairLFactor (h : PairLPolynomialExists q ψ abv μ ν π σ) :
    (pairLFactor h : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions (pairLPolynomial h))⁻¹ :=
  rfl

theorem pairLFactor_eq (h : PairLPolynomialExists q ψ abv μ ν π σ)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P) :
    (pairLFactor h : RationalFunctions) = (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_pairLFactor, pairLPolynomial_eq h hP]

section EqualRank

variable {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

theorem pairLPolynomialExists_self_iff :
    PairLPolynomialExists q ψ abv μ ν π σ ↔
      NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π σ) :=
  exists_congr fun _ => isPairLPolynomial_self

/-- In equal rank the pair L-factor is the equal-rank L-factor. -/
theorem pairLFactor_self (h : PairLPolynomialExists q ψ abv μ ν π σ) :
    pairLFactor h = equalRankLFactor q ψ abv μ π σ (pairLPolynomialExists_self_iff.1 h) := by
  apply Units.ext
  rw [pairLFactor_eq h (pairLPolynomial_spec h),
    equalRankLFactor_eq q ψ abv μ π σ _ (isPairLPolynomial_self.1 (pairLPolynomial_spec h))]

end EqualRank

section UnequalRank

variable (j k : ℕ) {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}

/-- Each block of a pair with an L-polynomial has a normalized generator. -/
theorem PairLPolynomialExists.unequalRank (h : PairLPolynomialExists q ψ abv μ ν π σ) :
    NormalizedGeneratorExists
      (unequalRankZetaValues q ψ abv j k μ (rectangularMeasure ν j (n + 1)) π σ) :=
  ⟨pairLPolynomial h, (pairLPolynomial_spec h).isUnequalRankLPolynomial j k⟩

/-- In unequal rank the pair L-factor is the L-factor of every block. -/
theorem pairLFactor_eq_unequalRankLFactor (h : PairLPolynomialExists q ψ abv μ ν π σ) :
    pairLFactor h = unequalRankLFactor q ψ abv j k μ (rectangularMeasure ν j (n + 1)) π σ
      (h.unequalRank j k) := by
  apply Units.ext
  rw [pairLFactor_eq h (pairLPolynomial_spec h),
    unequalRankLFactor_eq q ψ abv j k μ _ π σ _
      ((pairLPolynomial_spec h).isUnequalRankLPolynomial j k)]

end UnequalRank

section Invariance

/-- The L-polynomial depends on the pair only up to equivalence. -/
theorem isPairLPolynomial_congr_equiv
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsPairLPolynomial q ψ abv μ ν π σ P ↔ IsPairLPolynomial q ψ abv μ ν π₂ σ₂ P := by
  by_cases hnr : n < r
  · simp only [isPairLPolynomial_of_lt hnr, unequalRankZetaValuesAt_eq_of_equiv _ _ _ _ _ _ _ _ φ φ']
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self, isPairLPolynomial_self, IsEqualRankLPolynomial,
        IsEqualRankLPolynomial, equalRankZetaValues_eq_of_equiv q ψ abv μ φ φ']
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

/-- The L-polynomial of `(π ⊗ χ, σ ⊗ χ⁻¹)` is that of `(π, σ)`. -/
theorem isPairLPolynomial_twist (χ : Fˣ →* ℂˣ) :
    IsPairLPolynomial q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) σ) P ↔
      IsPairLPolynomial q ψ abv μ ν π σ P := by
  by_cases hnr : n < r
  · simp only [isPairLPolynomial_of_lt hnr, unequalRankZetaValuesAt_twist]
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self, isPairLPolynomial_self]
      exact isEqualRankLPolynomial_twist q ψ abv χ μ π σ P
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

theorem pairLPolynomialExists_twist_iff (χ : Fˣ →* ℂˣ) :
    PairLPolynomialExists q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) σ) ↔
      PairLPolynomialExists q ψ abv μ ν π σ :=
  exists_congr fun _ => isPairLPolynomial_twist χ

/-- `L(s, (π ⊗ χ) × (σ ⊗ χ⁻¹)) = L(s, π × σ)`. -/
theorem pairLFactor_twist (χ : Fˣ →* ℂˣ)
    (h : PairLPolynomialExists q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
      (Langlands.twist ((χ⁻¹).comp determinant) σ)) :
    pairLFactor h = pairLFactor ((pairLPolynomialExists_twist_iff χ).1 h) := by
  apply Units.ext
  rw [pairLFactor_eq h ((isPairLPolynomial_twist χ).2 (pairLPolynomial_spec _)),
    coe_pairLFactor]

open scoped ENNReal in
/-- The L-polynomial does not depend on the normalization of the quotient measure. -/
theorem isPairLPolynomial_smul_measure [SigmaFinite ν.measure] {c : ℝ≥0∞} (hc₀ : c ≠ 0)
    (hc : c ≠ ∞) :
    IsPairLPolynomial q ψ abv (c • μ) ν π σ P ↔ IsPairLPolynomial q ψ abv μ ν π σ P := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr, isPairLPolynomial_of_lt hnr]
    refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_
    subst hr
    exact isUnequalRankLPolynomial_smul_measure q ψ abv j k μ _ hc₀ hc π σ P
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self, isPairLPolynomial_self]
      exact isEqualRankLPolynomial_smul_measure q ψ abv μ hc₀ hc π σ P
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

end Invariance

end PairRelation

section DualPair

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- `P` is the L-polynomial of the dual pair `(π^ι, σ^ι)` of inverse-transpose
pullbacks for `ψ⁻¹ = ψ.scale (-1)`, the pair on the left of the JPSS functional
equation. -/
def IsDualPairLPolynomial (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) : Prop :=
  IsPairLPolynomial q (ψ.scale (-1)) abv μ ν (inverseTransposePullback π)
    (inverseTransposePullback σ) P

/-- The L-polynomial of the dual pair exists. -/
def DualPairLPolynomialExists (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) : Prop :=
  PairLPolynomialExists q (ψ.scale (-1)) abv μ ν (inverseTransposePullback π)
    (inverseTransposePullback σ)

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W} {P : ℂ[X]}

/-- The L-factor `L(s, π^ι × σ^ι)` of the dual pair, from its existence proof. -/
def dualPairLFactor {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    (h : DualPairLPolynomialExists q ψ abv μ ν π σ) : RationalFunctionsˣ :=
  pairLFactor h

theorem dualPairLFactor_eq {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    (h : DualPairLPolynomialExists q ψ abv μ ν π σ)
    (hP : IsDualPairLPolynomial q ψ abv μ ν π σ P) :
    (dualPairLFactor h : RationalFunctions) = (algebraMap ℂ[X] RationalFunctions P)⁻¹ :=
  pairLFactor_eq h hP

/-- In equal rank the dual L-polynomial generates the dual-pair zeta values of
`LocalFactor`. -/
theorem isDualPairLPolynomial_self {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} :
    IsDualPairLPolynomial q ψ abv μ ν π σ P ↔
      IsNormalizedGenerator (dualEqualRankZetaValues q ψ abv μ π σ) P :=
  isPairLPolynomial_self

/-- In unequal rank the dual L-polynomial generates the dual-pair zeta values of every
block. -/
theorem IsDualPairLPolynomial.dualUnequalRank (j k : ℕ)
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    (h : IsDualPairLPolynomial q ψ abv μ ν π σ P) :
    IsNormalizedGenerator
      (dualUnequalRankZetaValues q ψ abv j k μ (rectangularMeasure ν j (n + 1)) π σ) P :=
  IsPairLPolynomial.isUnequalRankLPolynomial j k h

end DualPair

section PadicStatements

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The p-adic equal-rank analytic statement supplies the L-polynomial of every
equal-rank pair of Whittaker type, for every compatible quotient measure. -/
theorem EqualRankAnalyticStatement.pairLPolynomialExists {n : ℕ}
    (h : EqualRankAnalyticStatement.{uF, uV, uW} F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ ν : AdditiveHaarMeasure F.Carrier,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          IsOfWhittakerType n (standardCharacter ψ n) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let _ : MeasurableSpace F.Carrier := borel _
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ
  exact pairLPolynomialExists_self_iff.2
    (h.normalizedGeneratorExists ψ μ hμ V W π σ hπ hσ)

/-- The p-adic unequal-rank analytic statements of every block, together with the
common-generator statement, supply the L-polynomial of every unequal-rank pair of
Whittaker type. -/
theorem UnequalRankCommonGeneratorStatement.pairLPolynomialExists {n r : ℕ}
    (hC : UnequalRankCommonGeneratorStatement.{uF, uV, uW} F T n r)
    (hU : ∀ j k : ℕ, r = n + (j + k + 1) →
      UnequalRankAnalyticStatement.{uF, uV, uW} F T n j k) (hnr : n < r) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ ν : AdditiveHaarMeasure F.Carrier,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          IsOfWhittakerType r (standardCharacter ψ r) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let _ : MeasurableSpace F.Carrier := borel _
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  obtain ⟨P, hP⟩ := hC hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  refine ⟨P, (isPairLPolynomial_of_lt hnr).2 fun j k hr => ?_⟩
  have hPj := hP j k hr
  subst hr
  rw [unequalRankZetaValuesAt_rfl,
    (hU j k rfl ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').zetaValues_eq hπ hσ hℓ hℓ']
  exact hPj

end PadicStatements

end Langlands.RankinSelberg
