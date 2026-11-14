import Langlands.Representation.RankinSelberg.PairGammaTwistExchangeIntegrals
import Langlands.Representation.RankinSelberg.EqualRankSwapEquations

/-!
# Proof of the pair gamma twist exchange

The integral comparisons of `PairGammaTwistExchangeIntegrals` are transported through the
fixed-functional gamma equations, the full gamma-factor relations (all compatible quotient
measures and all nonzero functionals), both rank branches of `IsPairGammaFactor`, and
finally the symmetric p-adic relation in either rank order.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV uW

namespace PairGammaTwistExchange

section RationalAlgebra

/-- Multiplying the minus-one scalar by `a` multiplies the dual continuation by `a^e`. -/
theorem gammaEquation_scale {q e : ℕ} {ζ a : ℂˣ} {κ : ℂ} (hκ : (a : ℂ) ^ e = κ)
    {G R Rdual : RationalFunctions} (h : GammaFunctionalEquation q ζ e G R Rdual) :
    GammaFunctionalEquation q (ζ * a) e G R (RatFunc.C κ * Rdual) := by
  subst κ
  have hκ0 : (a : ℂ) ^ e ≠ 0 := pow_ne_zero _ a.ne_zero
  intro s hR hnew hG
  have hd : Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0 :=
    (denom_eval_const_mul_ne_zero_iff _ hκ0 Rdual _).mp hnew
  have hC : Polynomial.eval₂ (RingHom.id ℂ) (spectralPoint q (1 - s))
      (RatFunc.C ((a : ℂ) ^ e)).denom ≠ 0 := by
    rw [RatFunc.denom_C, Polynomial.eval₂_one]
    exact one_ne_zero
  rw [RatFunc.eval_mul (RingHom.id ℂ) (spectralPoint q (1 - s)) hC hd, RatFunc.eval_C,
    h s hR hd hG, Units.val_mul, mul_pow, RingHom.id_apply]
  ring

/-- A minus-one change whose `e`-th power is trivial keeps the dual continuation. -/
theorem gammaEquation_scale_one {q e : ℕ} {ζ a : ℂˣ} (ha : (a : ℂ) ^ e = 1)
    {G R Rdual : RationalFunctions} (h : GammaFunctionalEquation q ζ e G R Rdual) :
    GammaFunctionalEquation q (ζ * a) e G R Rdual := by
  simpa only [map_one, one_mul] using gammaEquation_scale ha h

/-- The change of minus-one scalar raised to the larger rank index is the dual sign. -/
theorem sign_exponent_val {F : Type uF} [Field F] (χ : Fˣ →* ℂˣ) (n r : ℕ) (hnr : n ≤ r) :
    (((χ (-1) ^ (n + 1) : ℂˣ) : ℂ)) ^ r = (χ (-1) : ℂ) ^ ((n + 1) * (r - n)) := by
  have h := congrArg Units.val (sign_exponent χ n r hnr)
  push_cast at h ⊢
  exact h.symm

/-- In equal rank the change of minus-one scalar raised to the rank index is trivial. -/
theorem sign_exponent_self {F : Type uF} [Field F] (χ : Fˣ →* ℂˣ) (n : ℕ) :
    (((χ (-1) ^ (n + 1) : ℂˣ) : ℂ)) ^ n = 1 := by
  rw [sign_exponent_val χ n n le_rfl, Nat.sub_self, mul_zero, pow_zero]

/-- The dual sign squares to one. -/
theorem sign_mul_self {F : Type uF} [Field F] (χ : Fˣ →* ℂˣ) (e : ℕ) (y : ℂ) :
    (χ (-1) : ℂ) ^ e * ((χ (-1) : ℂ) ^ e * y) = y := by
  rw [← mul_assoc, ← mul_pow, character_negOne_mul_self, one_pow, one_mul]

end RationalAlgebra

section UnequalEquations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  (abv : AbsoluteValue F ℝ)
  {r n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

omit [IsTopologicalRing F] in
/-- The forward continuation sets of each block agree. -/
theorem unequal_values (j k : ℕ) (hr : r = n + (j + k + 1)) (q : ℕ)
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    unequalRankValuesAt j k hr q ψ abv μ ν (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' =
    unequalRankValuesAt j k hr q ψ abv μ ν π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') := by
  ext R
  rw [unequalRankValuesAt_eq, unequalRankValuesAt_eq]
  constructor
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, by
      rwa [unequal_forward ψ χ abv μ π σ ℓ ℓ' v z j k hr ν] at hR⟩
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, by
      rwa [← unequal_forward ψ χ abv μ π σ ℓ ℓ' v z j k hr ν] at hR⟩

/-- The fixed-functional unequal-rank gamma equation moves the twist to the test factor.
The minus-one scalar changes by `χ(-1)^(n+1)` and the dual continuation by the sign
`χ(-1)^((n+1)(r-n))`. -/
theorem unequal_equation (hn : n < r) (ν : AdditiveHaarMeasure F) (q : ℕ)
    (G : RationalFunctions) (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    UnequalRankGammaEquation hn q ψ abv μ ν (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' G ↔
    UnequalRankGammaEquation hn q ψ abv μ ν π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') G := by
  have hκ := sign_exponent_val χ n r hn.le
  constructor
  · rintro ⟨ζ, hζ, hall⟩
    refine ⟨ζ * χ (-1) ^ (n + 1), minusOne_twist hζ, ?_⟩
    intro j k hr
    obtain ⟨hnonzero, hFE⟩ := hall j k hr
    refine ⟨?_, ?_⟩
    · rwa [unequal_values ψ χ abv μ π σ j k hr q _ ℓ ℓ'] at hnonzero
    · intro f f'
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ z)
      refine ⟨R, RatFunc.C ((χ (-1) : ℂ) ^ ((n + 1) * (r - n))) * Rd, ?_, ?_,
        gammaEquation_scale hκ heq⟩
      · rwa [unequal_forward ψ χ abv μ π σ ℓ ℓ' v z j k hr] at hR
      · have hd := hasRationalContinuation_const_mul
          ((χ (-1) : ℂ) ^ ((n + 1) * (r - n))) hRd
        have hi : (fun s => (χ (-1) : ℂ) ^ ((n + 1) * (r - n)) *
            dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν
              (Langlands.twist (χ.comp determinant) π) σ (twisted χ π ℓ) ℓ'
              (modelMap _ _ v) (modelMap _ _ z) s) =
            dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν π
              (Langlands.twist (χ.comp determinant) σ) ℓ (twisted χ σ ℓ')
              (modelMap _ _ v) (modelMap _ _ z) := by
          rw [unequal_dual ψ χ abv μ π σ ℓ ℓ' v z hn j k hr ν]
          funext s
          exact sign_mul_self χ _ _
        rwa [hi] at hd
  · rintro ⟨ζ, hζ, hall⟩
    refine ⟨ζ * χ (-1) ^ (n + 1), minusOne_untwist hζ, ?_⟩
    intro j k hr
    obtain ⟨hnonzero, hFE⟩ := hall j k hr
    refine ⟨?_, ?_⟩
    · rwa [← unequal_values ψ χ abv μ π σ j k hr q _ ℓ ℓ'] at hnonzero
    · intro f f'
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ z)
      refine ⟨R, RatFunc.C ((χ (-1) : ℂ) ^ ((n + 1) * (r - n))) * Rd, ?_, ?_,
        gammaEquation_scale hκ heq⟩
      · rwa [← unequal_forward ψ χ abv μ π σ ℓ ℓ' v z j k hr] at hR
      · rw [unequal_dual ψ χ abv μ π σ ℓ ℓ' v z hn j k hr ν]
        exact hasRationalContinuation_const_mul _ hRd

end UnequalEquations

section EqualEquations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

omit [IsTopologicalRing F] [MeasurableSpace F] in
/-- The equal-rank forward continuation sets agree. -/
theorem equal_values (q : ℕ) (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) :
    equalRankRationalValues q ψ abv μ (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' =
    equalRankRationalValues q ψ abv μ π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [equal_forward ψ χ abv μ π σ ℓ ℓ' v z Φ] at hR⟩
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [← equal_forward ψ χ abv μ π σ ℓ ℓ' v z Φ] at hR⟩

/-- The fixed-functional equal-rank gamma equation moves the twist to the second factor,
with the same Fourier pair and continuations; the minus-one scalar changes by
`χ(-1)^(n+1)`, whose `n`-th power is trivial. -/
theorem equal_equation (ν : AdditiveHaarMeasure F) (q : ℕ) (G : RationalFunctions)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) :
    EqualRankGammaEquation q ψ abv μ ν (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' G ↔
    EqualRankGammaEquation q ψ abv μ ν π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') G := by
  have ha := sign_exponent_self χ n
  constructor
  · rintro ⟨ζ, hζ, hnonzero, hFE⟩
    refine ⟨ζ * χ (-1) ^ (n + 1), minusOne_twist hζ, ?_, ?_⟩
    · rwa [equal_values ψ χ abv μ π σ q ℓ ℓ'] at hnonzero
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, gammaEquation_scale_one ha heq⟩
      · rwa [equal_forward ψ χ abv μ π σ ℓ ℓ' v z Φ] at hR
      · rwa [equal_dual ψ χ abv μ π σ ℓ ℓ' v z Φhat] at hRd
  · rintro ⟨ζ, hζ, hnonzero, hFE⟩
    refine ⟨ζ * χ (-1) ^ (n + 1), minusOne_untwist hζ, ?_, ?_⟩
    · rwa [← equal_values ψ χ abv μ π σ q ℓ ℓ'] at hnonzero
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, gammaEquation_scale_one ha heq⟩
      · rwa [← equal_forward ψ χ abv μ π σ ℓ ℓ' v z Φ] at hR
      · rwa [← equal_dual ψ χ abv μ π σ ℓ ℓ' v z Φhat] at hRd

end EqualEquations

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- The full unequal-rank relation, over all compatible measures and nonzero functionals. -/
theorem unequal_factor (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hn : n < r) (q : ℕ) (G : RationalFunctions) :
    IsUnequalRankGammaFactor hn q ψ abv ν (Langlands.twist (χ.comp determinant) π) σ G ↔
    IsUnequalRankGammaFactor hn q ψ abv ν π (Langlands.twist (χ.comp determinant) σ) G := by
  constructor
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨untwisted χ π ℓ, hℓ⟩, ⟨twisted χ σ ℓ', hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (unequal_equation ψ χ abv μ π σ hn ν q G L₀ (untwisted χ σ L₀')).mp
      (@hall hinv μ hμc (twisted χ π L₀) (untwisted χ σ L₀') hL₀ hL₀')
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨twisted χ π ℓ, hℓ⟩, ⟨untwisted χ σ ℓ', hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (unequal_equation ψ χ abv μ π σ hn ν q G (untwisted χ π L₀) L₀').mpr
      (@hall hinv μ hμc (untwisted χ π L₀) (twisted χ σ L₀') hL₀ hL₀')

/-- The full equal-rank relation, over all compatible measures and nonzero functionals. -/
theorem equal_factor (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (q : ℕ) (G : RationalFunctions) :
    IsEqualRankGammaFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π) σ G ↔
    IsEqualRankGammaFactor q ψ abv ν π (Langlands.twist (χ.comp determinant) σ) G := by
  constructor
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨untwisted χ π ℓ, hℓ⟩, ⟨twisted χ σ ℓ', hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (equal_equation ψ χ abv μ π σ ν q G L₀ (untwisted χ σ L₀')).mp
      (@hall hinv μ hμc (twisted χ π L₀) (untwisted χ σ L₀') hL₀ hL₀')
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨twisted χ π ℓ, hℓ⟩, ⟨untwisted χ σ ℓ', hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (equal_equation ψ χ abv μ π σ ν q G (untwisted χ π L₀) L₀').mpr
      (@hall hinv μ hμc (untwisted χ π L₀) (twisted χ σ L₀') hL₀ hL₀')

/-- All three rank branches of the pair relation (candidate rank `r + 1`, test rank `n + 1`). -/
theorem pair_factor (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (q : ℕ) (G : RationalFunctions) :
    IsPairGammaFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π) σ G ↔
    IsPairGammaFactor q ψ abv ν π (Langlands.twist (χ.comp determinant) σ) G := by
  by_cases hn : n < r
  · rw [isPairGammaFactor_of_lt hn, isPairGammaFactor_of_lt hn]
    exact unequal_factor ψ χ abv ν σ π hn q G
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairGammaFactor_self, isPairGammaFactor_self]
      exact equal_factor ψ χ abv ν σ π q G
    · have hlt : r < n := by omega
      exact ⟨fun h => (not_isPairGammaFactor_of_lt hlt h).elim,
        fun h => (not_isPairGammaFactor_of_lt hlt h).elim⟩

end Relations

/-- The p-adic pair relation, with the canonical topology, measures and absolute value. -/
theorem padic_pair {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ : F.Carrierˣ →* ℂˣ) (G : RationalFunctions) :
    IsPadicPairGammaFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ G ↔
      IsPadicPairGammaFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ) G := by
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
  exact pair_factor ψ χ (normalizedAbsoluteValue F.canonicalTopologicalData) ν σ π
    F.canonicalTopologicalData.residueCardinality G

end PairGammaTwistExchange

/-- A determinant twist moves between the two factors of a symmetric p-adic gamma
certificate, for arbitrary ranks in either order. -/
theorem pairGammaTwistExchange : PairGammaTwistExchangeStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ χ G
  unfold IsPadicSymmetricGammaFactor
  by_cases h : t ≤ r
  · simp only [h, ↓reduceIte]
    exact PairGammaTwistExchange.padic_pair F ψ ν π σ χ G
  · simp only [h, ↓reduceIte]
    exact (PairGammaTwistExchange.padic_pair F ψ ν σ π χ G).symm

end Langlands.RankinSelberg
