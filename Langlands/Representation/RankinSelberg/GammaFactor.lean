import Langlands.Representation.RankinSelberg.EpsilonFactor

/-!
# Gamma factors of pairs as relations on JPSS functional equations

`IsPairGammaFactor` says that the rational function `G` of `q^(-s)` is the
gamma factor `γ(s, π × σ, ψ)` of Henniart 1993 (2.3.4)-(2.3.5): the dual
integral at `1 - s` is `ζ^e G(q^(-s))` times the integral at `s`, for every
compatible quotient measure and every pair of nonzero Whittaker functionals.
No factor function is chosen and existence is not assumed. Uniqueness and
invariance under equivalence are proved.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW uV₂ uW₂

section GammaEquation

/-- The gamma functional equation for one pair of continuations: `Rdual` at
`q^(-(1-s))` equals `ζ^e G(q^(-s)) R(q^(-s))` wherever the three rational
functions are defined. -/
def GammaFunctionalEquation (q : ℕ) (ζ : ℂˣ) (e : ℕ) (G R Rdual : RationalFunctions) :
    Prop :=
  ∀ s : ℂ,
    R.denom.eval (spectralPoint q s) ≠ 0 →
    Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
    G.denom.eval (spectralPoint q s) ≠ 0 →
    Rdual.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) =
      (ζ : ℂ) ^ e * (G.eval (RingHom.id ℂ) (spectralPoint q s) *
        R.eval (RingHom.id ℂ) (spectralPoint q s))

/-- The gamma factor of a functional equation is unique once the continuation
`R` is nonzero. -/
theorem GammaFunctionalEquation.gamma_unique {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {G G' R Rdual : RationalFunctions} (hR : R ≠ 0)
    (h : GammaFunctionalEquation q ζ e G R Rdual)
    (h' : GammaFunctionalEquation q ζ e G' R Rdual) : G = G' := by
  have hnum : R.num ≠ 0 := RatFunc.num_ne_zero hR
  set bad : Set ℝ :=
    {t | R.denom.eval (spectralPoint q t) = 0} ∪ {t | R.num.eval (spectralPoint q t) = 0} ∪
      {t | G.denom.eval (spectralPoint q t) = 0} ∪
      {t | G'.denom.eval (spectralPoint q t) = 0} ∪
      {t | Rdual.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} with hbad_def
  have hbad : bad.Finite :=
    ((((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_spectralPoint_roots hq hnum)).union
      (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero G))).union
      (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero G'))).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rdual))
  have hU : ((fun t : ℝ => spectralPoint q t) '' badᶜ).Infinite :=
    hbad.infinite_compl.image (spectralPoint_ofReal_injective hq).injOn
  have hgood : ∀ t ∈ badᶜ, R.denom.eval (spectralPoint q t) ≠ 0 ∧
      R.num.eval (spectralPoint q t) ≠ 0 ∧ G.denom.eval (spectralPoint q t) ≠ 0 ∧
      G'.denom.eval (spectralPoint q t) ≠ 0 ∧
      Rdual.denom.eval (spectralPoint q (1 - (t : ℂ))) ≠ 0 := by
    intro t ht
    simp only [hbad_def, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    exact ⟨h1, h2, h3, h4, h5⟩
  apply rationalFunction_eq_of_infinite_eval_eq G G' _ hU
  · rintro x ⟨t, ht, rfl⟩
    exact (hgood t ht).2.2.1
  · rintro x ⟨t, ht, rfl⟩
    exact (hgood t ht).2.2.2.1
  · rintro x ⟨t, ht, rfl⟩
    obtain ⟨hden, hnum0, hG, hG', hdual⟩ := hgood t ht
    have hReval : RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R ≠ 0 := by
      simpa only [RatFunc.eval, eval₂_id] using div_ne_zero hnum0 hden
    have h12 := (h t hden hdual hG).symm.trans (h' t hden hdual hG')
    exact mul_right_cancel₀ hReval (mul_left_cancel₀ (pow_ne_zero _ ζ.ne_zero) h12)

end GammaEquation

section EqualRankEquation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- The equal-rank gamma functional equation for the specified functionals and
quotient measure: some integral has a nonzero rational continuation, and for
every model vector pair and Schwartz--Bruhat function the continuation of the
dual integral with the Fourier transform at `1 - s` is `ζ^n G(q^(-s))` times
the continuation of the integral at `s`, where `ζ` is the minus-one scalar of
the model of `σ`. -/
def EqualRankGammaEquation (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (G : RationalFunctions) : Prop :=
  ∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
    (∃ R ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ', R ≠ 0) ∧
    ∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ (Φhat : SchwartzBruhat (Fin (n + 1) → F)) (R Rdual : RationalFunctions),
        IsRowFourierPair ψ ν Φ Φhat ∧
        HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R ∧
        HasRationalContinuation q
          (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rdual ∧
        GammaFunctionalEquation q ζ n G R Rdual

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The equation depends on the functionals only through their coefficient models. -/
theorem EqualRankGammaEquation.congr_model {ℓ₂ : glFunctionals ψ n π₂}
    {ℓ₂' : glInverseFunctionals ψ n σ₂} {G : RationalFunctions}
    (hM : coefficientModel π ℓ = coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' = coefficientModel σ₂ ℓ₂') :
    EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G ↔
      EqualRankGammaEquation q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G := by
  unfold EqualRankGammaEquation HasModelMinusOneScalar equalRankRationalValues
    dualEqualRankModelIntegral equalRankModelIntegral
  rw [hM, hM']

/-- For a nonzero second functional and `q > 1`, the gamma factor of the
fixed-functional equation is unique. -/
theorem EqualRankGammaEquation.unique (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    {G G' : RationalFunctions}
    (h : EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G)
    (h' : EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G') : G = G' := by
  obtain ⟨ζ, hζ, ⟨R, ⟨f, f', Φ, hR⟩, hR0⟩, hFE⟩ := h
  obtain ⟨ζ', hζ', -, hFE'⟩ := h'
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ'
  obtain ⟨Φhat, R₁, Rd₁, hΦ₁, hR₁, hRd₁, hN₁⟩ := hFE f f' Φ
  obtain ⟨Φhat', R₂, Rd₂, hΦ₂, hR₂, hRd₂, hN₂⟩ := hFE' f f' Φ
  obtain rfl := hΦ₁.unique hΦ₂
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact hN₁.gamma_unique hq hR0 hN₂

/-- Pulling both functionals back along representation equivalences does not
change the equation. -/
theorem EqualRankGammaEquation.functionalPullback_iff (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) (ℓ₂ : glFunctionals ψ n π₂) (ℓ₂' : glInverseFunctionals ψ n σ₂)
    {G : RationalFunctions} :
    EqualRankGammaEquation q ψ abv μ ν π σ (functionalPullback φ ℓ₂)
        (functionalPullback φ' ℓ₂') G ↔
      EqualRankGammaEquation q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G :=
  EqualRankGammaEquation.congr_model (coefficientModel_functionalPullback φ ℓ₂)
    (coefficientModel_functionalPullback φ' ℓ₂')

end EqualRankEquation

section UnequalRankEquation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- The unequal-rank gamma functional equation (candidate rank `r + 1`, test rank
`n + 1 < r + 1`) for the specified functionals and quotient measure, for every
block `j`: some block-`j` integral has a nonzero rational continuation, and for
every model vector pair the continuation of the transformed block-`k` integral
at `1 - s` is `ζ^r G(q^(-s))` times the continuation of the block-`j` integral
at `s`. -/
def UnequalRankGammaEquation (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (G : RationalFunctions) : Prop :=
  ∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
    ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      (∃ R ∈ unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ ℓ ℓ', R ≠ 0) ∧
      ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation q
            (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
              f.val f'.val) R ∧
          HasRationalContinuation q
            (dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ' f f') Rdual ∧
          GammaFunctionalEquation q ζ r G R Rdual

variable {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The equation depends on the functionals only through their coefficient models. -/
theorem UnequalRankGammaEquation.congr_model {ℓ₂ : glFunctionals ψ r π₂}
    {ℓ₂' : glInverseFunctionals ψ n σ₂} {G : RationalFunctions}
    (hM : coefficientModel π ℓ = coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' = coefficientModel σ₂ ℓ₂') :
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G ↔
      UnequalRankGammaEquation hnr q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G := by
  unfold UnequalRankGammaEquation
  simp only [unequalRankValuesAt_eq]
  unfold HasModelMinusOneScalar dualUnequalRankModelIntegralAt
  rw [hM, hM']

/-- For a nonzero second functional and `q > 1`, the gamma factor of the
fixed-functional equation is unique; the block `j = 0` already determines it. -/
theorem UnequalRankGammaEquation.unique (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    {G G' : RationalFunctions}
    (h : UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G)
    (h' : UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G') : G = G' := by
  obtain ⟨ζ, hζ, hall⟩ := h
  obtain ⟨ζ', hζ', hall'⟩ := h'
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ'
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  obtain ⟨⟨R, hRmem, hR0⟩, hFE⟩ := hall 0 (r - n - 1) hr
  obtain ⟨-, hFE'⟩ := hall' 0 (r - n - 1) hr
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨f, f', hR⟩ := hRmem
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := hFE f f'
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ := hFE' f f'
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact hN₁.gamma_unique hq hR0 hN₂

/-- Pulling both functionals back along representation equivalences does not
change the equation. -/
theorem UnequalRankGammaEquation.functionalPullback_iff (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) (ℓ₂ : glFunctionals ψ r π₂) (ℓ₂' : glInverseFunctionals ψ n σ₂)
    {G : RationalFunctions} :
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ (functionalPullback φ ℓ₂)
        (functionalPullback φ' ℓ₂') G ↔
      UnequalRankGammaEquation hnr q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G :=
  UnequalRankGammaEquation.congr_model (coefficientModel_functionalPullback φ ℓ₂)
    (coefficientModel_functionalPullback φ' ℓ₂')

end UnequalRankEquation

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- `G` is the gamma factor `γ(s, π × σ, ψ) = G(q^(-s))` of the equal-rank pair
`(π, σ)`. A compatible quotient measure and nonzero functionals for both
representations exist, and the gamma functional equation holds for every
compatible quotient measure and every pair of nonzero functionals. -/
def IsEqualRankGammaFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n)) ∧
  (∃ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0) ∧
  (∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G

/-- `G` is the gamma factor of the pair `(π, σ)` of ranks `r + 1 > n + 1`, in the
same sense as `IsEqualRankGammaFactor`. Only the quotient measure of the smaller
rank occurs. -/
def IsUnequalRankGammaFactor (hnr : n < r) (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n)) ∧
  (∃ ℓ : glFunctionals ψ r π, ℓ.val ≠ 0) ∧
  (∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G

/-- The gamma-factor relation for a candidate `π` of rank `r + 1` and a test `σ`
of rank `n + 1`. It is the unequal-rank relation when `n < r`, the equal-rank
relation when `r = n`, and false when the test rank is larger. -/
def IsPairGammaFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  if hnr : n < r then IsUnequalRankGammaFactor hnr q ψ abv ν π σ G
  else if hrn : r = n then
    IsEqualRankGammaFactor (n := n) q ψ abv ν (hrn ▸ π) σ G
  else False

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {G G' : RationalFunctions}

section EqualRank

variable {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- The equal-rank gamma factor is unique when `q > 1`. -/
theorem IsEqualRankGammaFactor.unique (hq : 1 < q)
    (h : IsEqualRankGammaFactor q ψ abv ν π σ G)
    (h' : IsEqualRankGammaFactor q ψ abv ν π σ G') : G = G' := by
  obtain ⟨⟨hinv, μ, hμ⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  obtain ⟨-, -, -, hall'⟩ := h'
  exact (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').unique hq hℓ' (@hall' hinv μ hμ ℓ ℓ' hℓ hℓ')

/-- The equal-rank relation transfers along representation equivalences. -/
theorem IsEqualRankGammaFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsEqualRankGammaFactor q ψ abv ν π σ G) :
    IsEqualRankGammaFactor q ψ abv ν π₂ σ₂ G := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ, ⟨functionalPullback φ.symm ℓ, functionalPullback_ne_zero φ.symm hℓ⟩,
    ⟨functionalPullback φ'.symm ℓ', functionalPullback_ne_zero φ'.symm hℓ'⟩, ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (EqualRankGammaEquation.functionalPullback_iff φ φ' ℓ₂ ℓ₂').mp
    (@hall hinv μ hμc _ _ (functionalPullback_ne_zero φ hℓ₂)
      (functionalPullback_ne_zero φ' hℓ₂'))

/-- The equal-rank relation is invariant under representation equivalences. -/
theorem IsEqualRankGammaFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsEqualRankGammaFactor q ψ abv ν π σ G ↔ IsEqualRankGammaFactor q ψ abv ν π₂ σ₂ G :=
  ⟨IsEqualRankGammaFactor.of_equiv φ φ', IsEqualRankGammaFactor.of_equiv φ.symm φ'.symm⟩

end EqualRank

section UnequalRank

variable {hnr : n < r} {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- The unequal-rank gamma factor is unique when `q > 1`. -/
theorem IsUnequalRankGammaFactor.unique (hq : 1 < q)
    (h : IsUnequalRankGammaFactor hnr q ψ abv ν π σ G)
    (h' : IsUnequalRankGammaFactor hnr q ψ abv ν π σ G') : G = G' := by
  obtain ⟨⟨hinv, μ, hμ⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  obtain ⟨-, -, -, hall'⟩ := h'
  exact (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').unique hq hℓ' (@hall' hinv μ hμ ℓ ℓ' hℓ hℓ')

/-- The unequal-rank relation transfers along representation equivalences. -/
theorem IsUnequalRankGammaFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsUnequalRankGammaFactor hnr q ψ abv ν π σ G) :
    IsUnequalRankGammaFactor hnr q ψ abv ν π₂ σ₂ G := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ, ⟨functionalPullback φ.symm ℓ, functionalPullback_ne_zero φ.symm hℓ⟩,
    ⟨functionalPullback φ'.symm ℓ', functionalPullback_ne_zero φ'.symm hℓ'⟩, ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (UnequalRankGammaEquation.functionalPullback_iff φ φ' ℓ₂ ℓ₂').mp
    (@hall hinv μ hμc _ _ (functionalPullback_ne_zero φ hℓ₂)
      (functionalPullback_ne_zero φ' hℓ₂'))

/-- The unequal-rank relation is invariant under representation equivalences. -/
theorem IsUnequalRankGammaFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsUnequalRankGammaFactor hnr q ψ abv ν π σ G ↔
      IsUnequalRankGammaFactor hnr q ψ abv ν π₂ σ₂ G :=
  ⟨IsUnequalRankGammaFactor.of_equiv φ φ', IsUnequalRankGammaFactor.of_equiv φ.symm φ'.symm⟩

end UnequalRank

section Pair

variable {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

theorem isPairGammaFactor_of_lt (hnr : n < r) :
    IsPairGammaFactor q ψ abv ν π σ G ↔ IsUnequalRankGammaFactor hnr q ψ abv ν π σ G := by
  rw [IsPairGammaFactor, dite_eq_left hnr]

theorem isPairGammaFactor_self {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} :
    IsPairGammaFactor q ψ abv ν π σ G ↔ IsEqualRankGammaFactor q ψ abv ν π σ G := by
  rw [IsPairGammaFactor, dite_eq_right (lt_irrefl n), dite_eq_left rfl]

/-- There is no gamma factor when the test rank exceeds the candidate rank. -/
theorem not_isPairGammaFactor_of_lt (hrn : r < n) : ¬ IsPairGammaFactor q ψ abv ν π σ G := by
  rw [IsPairGammaFactor, dite_eq_right (by omega), dite_eq_right (by omega)]
  exact id

/-- The pair gamma factor is unique when `q > 1`. -/
theorem IsPairGammaFactor.unique (hq : 1 < q) (h : IsPairGammaFactor q ψ abv ν π σ G)
    (h' : IsPairGammaFactor q ψ abv ν π σ G') : G = G' := by
  by_cases hnr : n < r
  · rw [isPairGammaFactor_of_lt hnr] at h h'
    exact h.unique hq h'
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairGammaFactor_self] at h h'
      exact h.unique hq h'
    · exact absurd h (not_isPairGammaFactor_of_lt (by omega))

/-- The pair relation transfers along representation equivalences. -/
theorem IsPairGammaFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsPairGammaFactor q ψ abv ν π σ G) : IsPairGammaFactor q ψ abv ν π₂ σ₂ G := by
  by_cases hnr : n < r
  · rw [isPairGammaFactor_of_lt hnr] at h ⊢
    exact h.of_equiv φ φ'
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairGammaFactor_self] at h ⊢
      exact h.of_equiv φ φ'
    · exact absurd h (not_isPairGammaFactor_of_lt (by omega))

/-- The pair relation is invariant under representation equivalences. -/
theorem IsPairGammaFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsPairGammaFactor q ψ abv ν π σ G ↔ IsPairGammaFactor q ψ abv ν π₂ σ₂ G :=
  ⟨IsPairGammaFactor.of_equiv φ φ', IsPairGammaFactor.of_equiv φ.symm φ'.symm⟩

end Pair

end Relations

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The gamma-factor relation for actual representations of `GL_(r+1)(F)` and
`GL_(n+1)(F)` over a p-adic field with its canonical topological data: `q` is
the residue cardinality and the absolute value is the normalized one. -/
def IsPadicPairGammaFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (G : RationalFunctions) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  IsPairGammaFactor F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν π σ G

/-- The p-adic gamma factor is unique. -/
theorem IsPadicPairGammaFactor.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {G G' : RationalFunctions} (h : IsPadicPairGammaFactor F ψ ν π σ G)
    (h' : IsPadicPairGammaFactor F ψ ν π σ G') : G = G' := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact IsPairGammaFactor.unique (PadicField.TopologicalData.residueCardinality_gt_one _) h h'

/-- The p-adic gamma-factor relation is invariant under representation
equivalences. -/
theorem IsPadicPairGammaFactor.congr_equiv {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {G : RationalFunctions} :
    IsPadicPairGammaFactor F ψ ν π σ G ↔ IsPadicPairGammaFactor F ψ ν π₂ σ₂ G := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact IsPairGammaFactor.congr_equiv φ φ'

/-- The gamma-factor relation on supercuspidal isomorphism classes of a p-adic
field with its canonical topological data. The candidate class `π` has rank
`r + 1` and the test class `τ` has rank `n + 1`. -/
def IsClassGammaFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (G : RationalFunctions) : Prop :=
  letI := F.canonicalTopologicalData.topology
  Quotient.lift₂
    (fun (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
        (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)) =>
      IsPadicPairGammaFactor F ψ ν A.obj.representation B.obj.representation G)
    (by
      rintro A B A' B' ⟨i⟩ ⟨j⟩
      exact propext (IsPadicPairGammaFactor.congr_equiv
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso i))
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso j))))
    π τ

/-- On representatives the class relation is the p-adic pair relation. -/
theorem isClassGammaFactor_mk (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) {r n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
    (B : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1))
    (G : RationalFunctions) :
    IsClassGammaFactor F ψ ν (Quotient.mk _ A) (Quotient.mk _ B) G ↔
      letI := F.canonicalTopologicalData.topology
      IsPadicPairGammaFactor F ψ ν A.obj.representation B.obj.representation G :=
  Iff.rfl

/-- The class-level gamma factor is unique. -/
theorem IsClassGammaFactor.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier} {r n : ℕ}
    {π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r)}
    {τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n)}
    {G G' : RationalFunctions} (h : IsClassGammaFactor F ψ ν π τ G)
    (h' : IsClassGammaFactor F ψ ν π τ G') : G = G' := by
  revert h h'
  refine Quotient.inductionOn₂ π τ ?_
  intro A B h h'
  exact IsPadicPairGammaFactor.unique h h'

end Padic

end Langlands.RankinSelberg
