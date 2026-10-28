import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuationFamily
import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof

/-!
# Covariance of the block-zero continuation families

The actual original `(0,k)` integral and the actual inverse-transpose `(k,0)`
integral of the dual model vectors transform by explicit factors under the two
covariance operations of JPSS (2.11.2) and (2.11.4): simultaneous right
translation by `diag(g, I)` and `g`, and right translation of the first vector by
an element of `U_(n+2,r+1)`. The unique rational continuations are then multiplied
by the corresponding monomials.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section Weights

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ) {d : ℕ}

/-- The determinant weight of an inverse transpose has the negated exponent. -/
theorem determinantWeight_inverseTranspose (g : Langlands.GeneralLinear d F) (s : ℂ) :
    determinantWeight abv (inverseTranspose d F g) s = determinantWeight abv g (-s) := by
  unfold determinantWeight
  rw [abv_det_inverseTranspose, Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg (abv.nonneg _)]
  exact Real.pi_ne_zero.symm

end Weights

section Embedding

variable {F : Type uF} [Field F] {n r : ℕ}

/-- Moving `diag(g, I)` through the inverse transpose of a right translate by the
block Weyl element replaces `g` by its inverse transpose. -/
theorem inverseTranspose_mul_embedding (hnr : n < r) (h : Langlands.GeneralLinear (r + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    inverseTranspose (r + 1) F (h * blockWeylAt n r hnr) *
        GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n) g) =
      inverseTranspose (r + 1) F (h *
        GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n) (inverseTranspose (n + 1) F g)) * blockWeylAt n r hnr) := by
  rw [mul_assoc h, ← blockWeylAt_mul_embedding hnr, ← mul_assoc,
    map_mul (inverseTranspose (r + 1) F) (h * blockWeylAt n r hnr),
    inverseTranspose_embedding hnr, inverseTranspose_involutive]

end Embedding

section IntegralLaws

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F))

/-- The translation law of `unequalRankIntegral_translate` for the transported
integral, with the reindexed embedding of the covariance predicate. -/
theorem unequalRankIntegralAt_translate [BorelSpace (LeftUnipotentQuotient n F)]
    {j k : ℕ} (hr : r = n + (j + k + 1))
    {ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin j) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * g.val) ∂ρ = determinantWeight abv g (-(j : ℂ)) * ∫ x, G x ∂ρ)
    {W₁ W₂ : WhittakerFunctions ψ r} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (hW : ∀ h, W₂.val h = W₁.val (h * GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega)) (appendIdentity n (r - n) g)))
    (hW' : ∀ h, W₂'.val h = W₁'.val (h * g)) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ρ W₂ W₂' s =
      determinantWeight abv g (((j + k + 1 : ℕ) : ℂ) / 2 - s - j) *
        unequalRankIntegralAt j k hr ψ abv μ ρ W₁ W₁' s := by
  subst hr
  refine unequalRankIntegral_translate ψ abv j k μ ρ hμ g hρ (fun h => ?_) hW' s
  rw [hW, reindex_appendIdentity_eq]

omit [IsTopologicalRing F] in
/-- JPSS (2.11.4) for the original block `(0,k)`: right translation of the first
function by `u ∈ U_(n+2,r+1)` multiplies the integral by `ψ_r(u)`. -/
theorem originalIntegralAt_unipotent {k : ℕ} (hr : r = n + (0 + k + 1))
    (ρ : Measure (Matrix (Fin 0) (Fin (n + 1)) F))
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u)
    {W₁ W₂ : WhittakerFunctions ψ r} (hW : ∀ h, W₂.val h = W₁.val (h * u.val))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegralAt 0 k hr ψ abv μ ρ W₂ W' s =
      (standardCharacter ψ r u : ℂ) * unequalRankIntegralAt 0 k hr ψ abv μ ρ W₁ W' s := by
  subst hr
  refine unequalRankIntegral_of_inner_change ψ abv 0 k μ ρ id _ (fun g x => ?_)
    (fun G => rfl) s
  obtain ⟨u', hsum, hu'⟩ := originalUnipotent_identity k u hu g
  rw [unequalRankMatrix_zero_rows, id, unequalRankMatrix_zero_rows, hW, hu', W₁.property u',
    standardCharacter_apply, standardCharacter_apply, hsum]

/-- JPSS (2.11.4) for the inverse-transpose block `(k,0)` of the dual first
function: right translation of the original first function by
`u ∈ U_(n+2,r+1)` multiplies the transformed integral by `ψ_r(u)`, when the
rectangular measure is invariant under `x ↦ A x + c` with `det A = 1`. -/
theorem dualIntegralAt_unipotent (hnr : n < r) {k : ℕ} (hr : r = n + (k + 0 + 1))
    {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    (hρ : ∀ A : Matrix (Fin k) (Fin k) F, A.det = 1 →
      ∀ (c : Matrix (Fin k) (Fin (n + 1)) F) (G : Matrix (Fin k) (Fin (n + 1)) F → ℂ),
        ∫ x, G (A * x + c) ∂ρ = ∫ x, G x ∂ρ)
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u)
    {W₁ W₂ : WhittakerFunctions ψ r} (hW : ∀ h, W₂.val h = W₁.val (h * u.val))
    (W' : InverseWhittakerFunctions (ψ.scale (-1)) n) (s : ℂ) :
    unequalRankIntegralAt k 0 hr (ψ.scale (-1)) abv μ ρ
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₂) (blockWeylAt n r hnr))
        W' s =
      (standardCharacter ψ r u : ℂ) * unequalRankIntegralAt k 0 hr (ψ.scale (-1)) abv μ ρ
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₁) (blockWeylAt n r hnr))
        W' s := by
  subst hr
  obtain ⟨n₀, A, c, hA, hsum, hid⟩ := dualUnipotent_identity k hnr u hu
  refine unequalRankIntegral_of_inner_change (ψ.scale (-1)) abv k 0 μ ρ (fun x => A * x + c) _
    (fun g x => ?_) (hρ A hA c) s
  have key : inverseTranspose _ F (unequalRankMatrix k 0 g x * blockWeylAt n _ hnr) * u.val =
      inverseTranspose _ F (n₀.val * (unequalRankMatrix k 0 g (A * x + c) *
        blockWeylAt n _ hnr)) := by
    rw [← mul_assoc, ← hid, map_mul (inverseTranspose _ F)
      (unequalRankMatrix k 0 g x * blockWeylAt n _ hnr), inverseTranspose_involutive]
  have h1 : (firstDualFunction ψ _ W₂).val (unequalRankMatrix k 0 g x * blockWeylAt n _ hnr) =
      (firstDualFunction ψ _ W₁).val
        (n₀.val * (unequalRankMatrix k 0 g (A * x + c) * blockWeylAt n _ hnr)) := by
    rw [firstDualFunction_apply, firstDualFunction_apply, hW, mul_assoc, key]
  change (firstDualFunction ψ _ W₂).val (unequalRankMatrix k 0 g x * blockWeylAt n _ hnr) =
    _ * (firstDualFunction ψ _ W₁).val (unequalRankMatrix k 0 g (A * x + c) * blockWeylAt n _ hnr)
  rw [h1, (firstDualFunction ψ _ W₁).property n₀]
  congr 1
  rw [standardCharacter_apply, standardCharacter_apply, hsum]
  change ψ.complex ((↑(-1 : Fˣ) : F) * _) = _
  simp only [Units.val_neg, Units.val_one, neg_one_mul, neg_neg]

/-- JPSS (2.11.2) for the inverse-transpose block `(k,0)` of the dual model
functions: simultaneous right translation of the original functions by
`diag(g, I)` and `g` translates the dual functions by the inverse transpose. -/
theorem dualIntegralAt_translate [BorelSpace (LeftUnipotentQuotient n F)]
    (hnr : n < r) {k : ℕ} (hr : r = n + (k + 0 + 1))
    {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin k) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * (inverseTranspose (n + 1) F g).val) ∂ρ =
        determinantWeight abv (inverseTranspose (n + 1) F g) (-(k : ℂ)) * ∫ x, G x ∂ρ)
    {W₁ W₂ : WhittakerFunctions ψ r} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (hW : ∀ h, W₂.val h = W₁.val (h * GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega)) (appendIdentity n (r - n) g)))
    (hW' : ∀ h, W₂'.val h = W₁'.val (h * g)) (s : ℂ) :
    unequalRankIntegralAt k 0 hr (ψ.scale (-1)) abv μ ρ
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₂) (blockWeylAt n r hnr))
        (secondDualFunction ψ n W₂') s =
      determinantWeight abv (inverseTranspose (n + 1) F g)
          (((k + 0 + 1 : ℕ) : ℂ) / 2 - s - k) *
        unequalRankIntegralAt k 0 hr (ψ.scale (-1)) abv μ ρ
          (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₁) (blockWeylAt n r hnr))
          (secondDualFunction ψ n W₁') s := by
  refine unequalRankIntegralAt_translate (ψ.scale (-1)) abv μ hr hμ
    (inverseTranspose (n + 1) F g) hρ (fun h => ?_) (fun h => ?_) s
  · rw [translateWhittaker_apply, translateWhittaker_apply, firstDualFunction_apply,
      firstDualFunction_apply, hW, mul_assoc, inverseTranspose_mul_embedding hnr]
  · rw [secondDualFunction_apply, secondDualFunction_apply, hW', mul_assoc, map_mul,
      inverseTranspose_involutive]

end IntegralLaws

section Families

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- Simultaneous right translation multiplies the continuation of block `(j,k)`
by a constant times `X^m`, where `|det g| = q^m`. -/
theorem blockContinuationFamily_translate [BorelSpace (LeftUnipotentQuotient n F)]
    {j k : ℕ} {hr : r = n + (j + k + 1)} {ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
    (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ρ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin j) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * g.val) ∂ρ = determinantWeight abv g (-(j : ℂ)) * ∫ x, G x ∂ρ)
    (m : ℤ) (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    {f₁ f₂ : (coefficientModel π ℓ).toSubmodule} {f₁' f₂' : (coefficientModel σ ℓ').toSubmodule}
    (hW : ∀ h, f₂.val.val h = f₁.val.val (h * GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega)) (appendIdentity n (r - n) g)))
    (hW' : ∀ h, f₂'.val.val h = f₁'.val.val (h * g)) :
    blockContinuationFamily hq hA f₂ f₂' =
      RatFunc.C (determinantWeight abv g (((j + k + 1 : ℕ) : ℂ) / 2 - j)) * RatFunc.X ^ m *
        blockContinuationFamily hq hA f₁ f₁' :=
  blockContinuationFamily_of_integral hq hA _ m fun t => by
    rw [unequalRankIntegralAt_translate ψ abv μ hr hμ g hρ hW hW' t,
      show ((j + k + 1 : ℕ) : ℂ) / 2 - t - j = (((j + k + 1 : ℕ) : ℂ) / 2 - j) + -t by ring,
      determinantWeight_exponent_add,
      determinantWeight_neg_eq_spectralPoint_zpow (by omega) abv g m hg t]

omit [IsTopologicalRing F] in
/-- Right translation of the first vector by `u ∈ U_(n+2,r+1)` multiplies the
original continuation by `ψ_r(u)`. -/
theorem originalContinuationFamily_unipotent {k : ℕ} {hr : r = n + (0 + k + 1)}
    {ρ : Measure (Matrix (Fin 0) (Fin (n + 1)) F)} (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hA : UnequalRankAnalyticAt 0 k hr q ψ abv μ ρ π σ ℓ ℓ')
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    blockContinuationFamily hq hA (modelRepresentation π ℓ u.val f) f' =
      RatFunc.C (standardCharacter ψ r u : ℂ) * RatFunc.X ^ (0 : ℤ) *
        blockContinuationFamily hq hA f f' :=
  blockContinuationFamily_of_integral hq hA _ 0 fun t => by
    rw [zpow_zero, mul_one]
    exact originalIntegralAt_unipotent ψ abv μ hr ρ u hu (fun h => rfl) f'.val t

variable (ψ π σ ℓ ℓ') in
/-- The actual first dual model map `f ↦ R(diag(I, w)) F̂`. -/
abbrev dualFirstModelMap (hnr : n < r) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)).toSubmodule :=
  (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr)).toLinearMap

/-- Right translation of the first original vector by `u ∈ U_(n+2,r+1)`
multiplies the inverse-transpose continuation of the dual vectors by `ψ_r(u)`. -/
theorem dualContinuationFamily_unipotent (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)}
    {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)} (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hρ : ∀ A : Matrix (Fin k) (Fin k) F, A.det = 1 →
      ∀ (c : Matrix (Fin k) (Fin (n + 1)) F) (G : Matrix (Fin k) (Fin (n + 1)) F → ℂ),
        ∫ x, G (A * x + c) ∂ρ = ∫ x, G x ∂ρ)
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    blockContinuationFamily hq hAd
        (dualFirstModelMap ψ π ℓ hnr (modelRepresentation π ℓ u.val f))
        (secondDualModelMap ψ σ ℓ' f') =
      RatFunc.C (standardCharacter ψ r u : ℂ) * RatFunc.X ^ (0 : ℤ) *
        blockContinuationFamily hq hAd (dualFirstModelMap ψ π ℓ hnr f)
          (secondDualModelMap ψ σ ℓ' f') :=
  blockContinuationFamily_of_integral hq hAd _ 0 fun t => by
    rw [zpow_zero, mul_one]
    exact dualIntegralAt_unipotent ψ abv μ hnr hr hρ u hu (W₁ := f.val)
      (W₂ := (modelRepresentation π ℓ u.val f).val) (fun h => rfl) _ t

/-- Simultaneous right translation of the original vectors by `diag(g, I)` and
`g` multiplies the inverse-transpose continuation of the dual vectors by a
constant times `X^m`, where `|det g⁻ᵗ| = q^m`. -/
theorem dualContinuationFamily_translate [BorelSpace (LeftUnipotentQuotient n F)]
    (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)}
    {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)} (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin k) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * (inverseTranspose (n + 1) F g).val) ∂ρ =
        determinantWeight abv (inverseTranspose (n + 1) F g) (-(k : ℂ)) * ∫ x, G x ∂ρ)
    (m : ℤ) (hg : abv (Matrix.det (inverseTranspose (n + 1) F g).val) = (q : ℝ) ^ m)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    blockContinuationFamily hq hAd
        (dualFirstModelMap ψ π ℓ hnr (modelRepresentation π ℓ
          (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
            (appendIdentity n (r - n) g)) f))
        (secondDualModelMap ψ σ ℓ' (modelRepresentation σ ℓ' g f')) =
      RatFunc.C (determinantWeight abv (inverseTranspose (n + 1) F g)
          (((k + 0 + 1 : ℕ) : ℂ) / 2 - k)) * RatFunc.X ^ m *
        blockContinuationFamily hq hAd (dualFirstModelMap ψ π ℓ hnr f)
          (secondDualModelMap ψ σ ℓ' f') :=
  blockContinuationFamily_of_integral hq hAd _ m fun t => by
    have h := dualIntegralAt_translate ψ abv μ hnr hr hμ g hρ (W₁ := f.val) (W₁' := f'.val)
      (W₂ := (modelRepresentation π ℓ (GeneralLinear.reindex
        (finCongr (show n + (r - n) + 1 = r + 1 by omega)) (appendIdentity n (r - n) g)) f).val)
      (W₂' := (modelRepresentation σ ℓ' g f').val) (fun h => rfl) (fun h => rfl) t
    rw [show ((k + 0 + 1 : ℕ) : ℂ) / 2 - t - k = (((k + 0 + 1 : ℕ) : ℂ) / 2 - k) + -t by ring,
      determinantWeight_exponent_add,
      determinantWeight_neg_eq_spectralPoint_zpow (by omega) abv _ m hg t] at h
    exact h

end Families

end Langlands.RankinSelberg
