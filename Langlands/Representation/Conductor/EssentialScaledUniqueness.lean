import Langlands.Representation.Conductor.Essential

/-!
# Vectors with a scaled essential identity are multiples of the essential vector

A Whittaker function whose corank-one integrals continue to `C ∏ i, P(x_i X)⁻¹`, and
whose restriction to `diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant, is `C` times
the essential vector once essential vectors are unique. This is the final step of
the proof of JPSS 1981, Theorem (5.1), printed page 214.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-! ### Rational continuations of scaled combinations -/

section Continuation

/-- Evaluating `C • R` at a point where the denominator of `R` does not vanish gives
`C` times the value of `R`. -/
theorem ratFunc_eval_smul {z : ℂ} {R : RatFunc ℂ} (hR : R.denom.eval z ≠ 0) (C : ℂ) :
    RatFunc.eval (RingHom.id ℂ) z (C • R) = C * RatFunc.eval (RingHom.id ℂ) z R := by
  rw [RatFunc.smul_eq_C_mul, RatFunc.eval_mul, RatFunc.eval_C, RingHom.id_apply]
  · rw [RatFunc.denom_C, Polynomial.eval₂_one]
    exact one_ne_zero
  · simpa only [Polynomial.eval₂_id] using hR

/-- A rational continuation may be checked on any smaller right half-plane. -/
theorem HasRationalContinuation.congr_eventually {q : ℕ} {f g : ℂ → ℂ} {R : RatFunc ℂ}
    (hf : HasRationalContinuation q f R) (b : ℝ) (hfg : ∀ s : ℂ, b < s.re → g s = f s) :
    HasRationalContinuation q g R := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hden, hfs⟩ := ha s ((le_max_left a b).trans_lt hs)
  exact ⟨hden, (hfg s ((le_max_right a b).trans_lt hs)).trans hfs⟩

/-- If `f` continues to `R` then `C f` continues to `C • R`. -/
theorem HasRationalContinuation.const_mul {q : ℕ} {f : ℂ → ℂ} {R : RatFunc ℂ}
    (hf : HasRationalContinuation q f R) (C : ℂ) :
    HasRationalContinuation q (fun s => C * f s) (C • R) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, fun s hs => ?_⟩
  obtain ⟨hden, hfs⟩ := ha s hs
  refine ⟨?_, ?_⟩
  · intro h0
    apply hden
    have hdvd : (C • R).denom ∣ R.denom := by
      rw [RatFunc.smul_eq_C_mul]
      refine (RatFunc.denom_mul_dvd _ _).trans ?_
      rw [RatFunc.denom_C, one_mul]
    obtain ⟨d, hd⟩ := hdvd
    rw [hd, Polynomial.eval_mul, h0, zero_mul]
  · show C * f s = _
    rw [hfs, ratFunc_eval_smul hden]

/-- If `f` continues to `R` and `g` to `C • R`, then `f + (g - C f)` continues to `R`. -/
theorem HasRationalContinuation.add_sub_const_mul {q : ℕ} {f g : ℂ → ℂ} {R : RatFunc ℂ}
    {C : ℂ} (hf : HasRationalContinuation q f R) (hg : HasRationalContinuation q g (C • R)) :
    HasRationalContinuation q (fun s => f s + (g s - C * f s)) R := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hden, hfs⟩ := ha s ((le_max_left a b).trans_lt hs)
  obtain ⟨-, hgs⟩ := hb s ((le_max_right a b).trans_lt hs)
  refine ⟨hden, ?_⟩
  show f s + (g s - C * f s) = _
  rw [hfs, hgs, ratFunc_eval_smul hden]
  ring

end Continuation

/-! ### Linearity of the corank-one integral in the Whittaker function -/

section Linear

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}

theorem corankOneIntegrand_add (W₁ W₂ : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegrand ψ abv (W₁ + W₂) W' s =
      corankOneIntegrand ψ abv W₁ W' s + corankOneIntegrand ψ abv W₂ W' s := by
  funext x
  induction x using Quotient.ind with
  | _ g =>
    change (W₁.val (rankInclusion 1 g) + W₂.val (rankInclusion 1 g)) * W'.val g *
        determinantWeight abv g (s - 1 / 2) =
      W₁.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2) +
        W₂.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2)
    ring

theorem corankOneIntegrand_sub (W₁ W₂ : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegrand ψ abv (W₁ - W₂) W' s =
      corankOneIntegrand ψ abv W₁ W' s - corankOneIntegrand ψ abv W₂ W' s := by
  funext x
  induction x using Quotient.ind with
  | _ g =>
    change (W₁.val (rankInclusion 1 g) - W₂.val (rankInclusion 1 g)) * W'.val g *
        determinantWeight abv g (s - 1 / 2) =
      W₁.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2) -
        W₂.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2)
    ring

theorem corankOneIntegrand_smul (C : ℂ) (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegrand ψ abv (C • W) W' s = C • corankOneIntegrand ψ abv W W' s := by
  funext x
  induction x using Quotient.ind with
  | _ g =>
    change (C * W.val (rankInclusion 1 g)) * W'.val g *
        determinantWeight abv g (s - 1 / 2) =
      C * (W.val (rankInclusion 1 g) * W'.val g * determinantWeight abv g (s - 1 / 2))
    ring

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))

theorem CorankOneConverges.add {W₁ W₂ : WhittakerFunctions ψ (n + 1)}
    {W' : InverseWhittakerFunctions ψ n} {s : ℂ}
    (h₁ : CorankOneConverges ψ abv μ W₁ W' s) (h₂ : CorankOneConverges ψ abv μ W₂ W' s) :
    CorankOneConverges ψ abv μ (W₁ + W₂) W' s := by
  unfold CorankOneConverges at *
  rw [corankOneIntegrand_add]
  exact h₁.add h₂

theorem CorankOneConverges.sub {W₁ W₂ : WhittakerFunctions ψ (n + 1)}
    {W' : InverseWhittakerFunctions ψ n} {s : ℂ}
    (h₁ : CorankOneConverges ψ abv μ W₁ W' s) (h₂ : CorankOneConverges ψ abv μ W₂ W' s) :
    CorankOneConverges ψ abv μ (W₁ - W₂) W' s := by
  unfold CorankOneConverges at *
  rw [corankOneIntegrand_sub]
  exact h₁.sub h₂

theorem CorankOneConverges.smul {W : WhittakerFunctions ψ (n + 1)}
    {W' : InverseWhittakerFunctions ψ n} {s : ℂ}
    (h : CorankOneConverges ψ abv μ W W' s) (C : ℂ) :
    CorankOneConverges ψ abv μ (C • W) W' s := by
  unfold CorankOneConverges at *
  rw [corankOneIntegrand_smul]
  exact h.smul C

theorem corankOneIntegral_add {W₁ W₂ : WhittakerFunctions ψ (n + 1)}
    {W' : InverseWhittakerFunctions ψ n} {s : ℂ}
    (h₁ : CorankOneConverges ψ abv μ W₁ W' s) (h₂ : CorankOneConverges ψ abv μ W₂ W' s) :
    corankOneIntegral ψ abv μ (W₁ + W₂) W' s =
      corankOneIntegral ψ abv μ W₁ W' s + corankOneIntegral ψ abv μ W₂ W' s := by
  unfold corankOneIntegral
  rw [corankOneIntegrand_add]
  exact integral_add h₁ h₂

theorem corankOneIntegral_sub {W₁ W₂ : WhittakerFunctions ψ (n + 1)}
    {W' : InverseWhittakerFunctions ψ n} {s : ℂ}
    (h₁ : CorankOneConverges ψ abv μ W₁ W' s) (h₂ : CorankOneConverges ψ abv μ W₂ W' s) :
    corankOneIntegral ψ abv μ (W₁ - W₂) W' s =
      corankOneIntegral ψ abv μ W₁ W' s - corankOneIntegral ψ abv μ W₂ W' s := by
  unfold corankOneIntegral
  rw [corankOneIntegrand_sub]
  exact integral_sub h₁ h₂

theorem corankOneIntegral_smul (C : ℂ) (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegral ψ abv μ (C • W) W' s = C * corankOneIntegral ψ abv μ W W' s := by
  unfold corankOneIntegral
  rw [corankOneIntegrand_smul]
  exact integral_smul C _

end Linear

/-! ### The scaled essential identity -/

section Scaled

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable (μ : Measure (LeftUnipotentQuotient n F))

/-- Jacquet's identity scaled by `C`: for every `x`, the corank-one integral of `W`
against `W(g; x; ψ̄)` converges on a right half-plane and has the rational continuation
`C ∏ i, P(x_i X)⁻¹`. -/
def SatisfiesScaledEssentialIdentity
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (P : ℂ[X]) (C : ℂ)
    (W : WhittakerFunctions ψ (n + 1)) : Prop :=
  ∀ x : Fin (n + 1) → ℂˣ,
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x) s) ∧
    HasRationalContinuation q
      (corankOneIntegral ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x))
      (C • essentialFactor P x)

variable {q ψ abv μ}
variable {hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1}
  {ϖ : Fˣ} {hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ}

/-- The scaled identity with `C = 1` is Jacquet's identity. -/
theorem satisfiesScaledEssentialIdentity_one_iff {P : ℂ[X]} {W : WhittakerFunctions ψ (n + 1)} :
    SatisfiesScaledEssentialIdentity q ψ abv μ hψ hϖ P 1 W ↔
      SatisfiesEssentialIdentity q ψ abv μ hψ hϖ P W := by
  simp only [SatisfiesScaledEssentialIdentity, SatisfiesEssentialIdentity, one_smul]

/-- Scaling a function satisfying Jacquet's identity by `C` gives the scaled identity. -/
theorem SatisfiesEssentialIdentity.smul {P : ℂ[X]} {W : WhittakerFunctions ψ (n + 1)}
    (hW : SatisfiesEssentialIdentity q ψ abv μ hψ hϖ P W) (C : ℂ) :
    SatisfiesScaledEssentialIdentity q ψ abv μ hψ hϖ P C (C • W) := by
  intro x
  obtain ⟨⟨a, ha⟩, hcont⟩ := hW x
  refine ⟨⟨a, fun s hs => CorankOneConverges.smul ψ abv μ (ha s hs) C⟩, ?_⟩
  have he : corankOneIntegral ψ abv μ (C • W) (inverseSphericalWhittaker hψ hϖ q x) =
      fun s => C * corankOneIntegral ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x) s := by
    funext s
    exact corankOneIntegral_smul ψ abv μ C W _ s
  rw [he]
  exact HasRationalContinuation.const_mul hcont C

/-- If `W` satisfies Jacquet's identity and `W₁` the identity scaled by `C`, then
`W + (W₁ - C W)` satisfies Jacquet's identity. -/
theorem SatisfiesEssentialIdentity.add_sub_smul {P : ℂ[X]} {C : ℂ}
    {W W₁ : WhittakerFunctions ψ (n + 1)}
    (hW : SatisfiesEssentialIdentity q ψ abv μ hψ hϖ P W)
    (hW₁ : SatisfiesScaledEssentialIdentity q ψ abv μ hψ hϖ P C W₁) :
    SatisfiesEssentialIdentity q ψ abv μ hψ hϖ P (W + (W₁ - C • W)) := by
  intro x
  obtain ⟨⟨a, ha⟩, hcont⟩ := hW x
  obtain ⟨⟨b, hb⟩, hcont₁⟩ := hW₁ x
  have hconv : ∀ s : ℂ, max a b < s.re →
      CorankOneConverges ψ abv μ (W + (W₁ - C • W)) (inverseSphericalWhittaker hψ hϖ q x) s ∧
      corankOneIntegral ψ abv μ (W + (W₁ - C • W)) (inverseSphericalWhittaker hψ hϖ q x) s =
        corankOneIntegral ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x) s +
          (corankOneIntegral ψ abv μ W₁ (inverseSphericalWhittaker hψ hϖ q x) s -
            C * corankOneIntegral ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x) s) := by
    intro s hs
    have h₀ := ha s ((le_max_left a b).trans_lt hs)
    have h₁ := hb s ((le_max_right a b).trans_lt hs)
    have hC := CorankOneConverges.smul ψ abv μ h₀ C
    have hD := CorankOneConverges.sub ψ abv μ h₁ hC
    refine ⟨CorankOneConverges.add ψ abv μ h₀ hD, ?_⟩
    rw [corankOneIntegral_add ψ abv μ h₀ hD, corankOneIntegral_sub ψ abv μ h₁ hC,
      corankOneIntegral_smul]
  refine ⟨⟨max a b, fun s hs => (hconv s hs).1⟩, ?_⟩
  exact HasRationalContinuation.congr_eventually
    (HasRationalContinuation.add_sub_const_mul hcont hcont₁) (max a b)
    (fun s hs => (hconv s hs).2)

end Scaled

/-! ### Restriction invariance of combinations -/

section Restriction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {ψ : UnitaryAdditiveCharacter F}
  {π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V}
  {ℓ : glFunctionals ψ (n + 1) π}

/-- Restriction invariance is preserved by the combination `w + (v - C w)`. -/
theorem IsIntegralInvariantOnRestriction.add_sub_smul {w v : (coefficientModel π ℓ).toSubmodule}
    (hw : IsIntegralInvariantOnRestriction π ℓ w) (hv : IsIntegralInvariantOnRestriction π ℓ v)
    (C : ℂ) : IsIntegralInvariantOnRestriction π ℓ (w + (v - C • w)) := by
  intro g k
  change w.val.val (rankInclusion 1 (g * k.val)) +
      (v.val.val (rankInclusion 1 (g * k.val)) - C * w.val.val (rankInclusion 1 (g * k.val))) =
    w.val.val (rankInclusion 1 g) +
      (v.val.val (rankInclusion 1 g) - C * w.val.val (rankInclusion 1 g))
  rw [hw g k, hv g k]

end Restriction

/-! ### Multiples of the essential vector -/

section Essential

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
  {π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V}
  {ℓ : glFunctionals ψ (n + 1) π}

/-- Adding to an essential vector `w` the difference `v - C w`, where `v` is restriction
invariant and satisfies the identity scaled by `C`, gives an essential vector. -/
theorem IsEssentialVector.add_sub_smul {w v : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w) (hv : IsIntegralInvariantOnRestriction π ℓ v)
    {P : ℂ[X]} (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) {C : ℂ}
    (hid : SatisfiesScaledEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P C v.val) :
    IsEssentialVector h π ℓ (w + (v - C • w)) :=
  ⟨⟨P, hP, (hw.satisfiesEssentialIdentity h π ℓ hP).add_sub_smul hid⟩,
    hw.2.add_sub_smul hv C⟩

/-- JPSS 1981, proof of Theorem (5.1), printed page 214, last step: when `w` is the only
essential vector, every restriction-invariant `v` satisfying Jacquet's identity scaled by
`C` equals `C w`. The case `C = 0` gives `v = 0`. -/
theorem eq_smul_of_satisfiesScaledEssentialIdentity {w v : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w)
    (huniq : ∀ u : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ u → u = w)
    (hv : IsIntegralInvariantOnRestriction π ℓ v)
    {P : ℂ[X]} (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) {C : ℂ}
    (hid : SatisfiesScaledEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P C v.val) :
    v = C • w := by
  have he := huniq _ (hw.add_sub_smul h hv hP hid)
  rw [add_eq_left] at he
  exact sub_eq_zero.mp he

/-- The same conclusion for the essential vector selected from unique existence. -/
theorem eq_smul_essentialVector_of_satisfiesScaledEssentialIdentity
    (hu : ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w)
    {v : (coefficientModel π ℓ).toSubmodule} (hv : IsIntegralInvariantOnRestriction π ℓ v)
    {P : ℂ[X]} (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) {C : ℂ}
    (hid : SatisfiesScaledEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P C v.val) :
    v = C • essentialVector h π ℓ hu :=
  eq_smul_of_satisfiesScaledEssentialIdentity h (essentialVector_spec h π ℓ hu)
    (fun u hu' => (isEssentialVector_iff_eq h π ℓ hu u).mp hu') hv hP hid

/-- Every multiple of an essential vector satisfies the correspondingly scaled identity
and restriction invariance, so the hypotheses above describe exactly the line of `w`. -/
theorem IsEssentialVector.smul {w : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w)
    {P : ℂ[X]} (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) (C : ℂ) :
    SatisfiesScaledEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P C (C • w).val ∧
      IsIntegralInvariantOnRestriction π ℓ (C • w) := by
  refine ⟨(hw.satisfiesEssentialIdentity h π ℓ hP).smul C, fun g k => ?_⟩
  change C * w.val.val (rankInclusion 1 (g * k.val)) = C * w.val.val (rankInclusion 1 g)
  rw [hw.2 g k]

/-- Line clause at a level `a`: if every level-`a` fixed vector of the model satisfies
Jacquet's identity scaled by some constant, and `w` is the only essential vector, then
every level-`a` fixed vector is a multiple of `w`. -/
theorem exists_eq_smul_of_mem_levelFixedVectors {w : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w)
    (huniq : ∀ u : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ u → u = w)
    {P : ℂ[X]} (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) {a : ℕ}
    (hscaled : ∀ v ∈ levelFixedVectors (V := (coefficientModel π ℓ).toSubmodule)
        (modelRepresentation π ℓ) a,
      ∃ C : ℂ, SatisfiesScaledEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P C
        v.val) :
    ∀ v ∈ levelFixedVectors (V := (coefficientModel π ℓ).toSubmodule)
        (modelRepresentation π ℓ) a, ∃ C : ℂ, v = C • w := by
  intro v hv
  obtain ⟨C, hC⟩ := hscaled v hv
  exact ⟨C, eq_smul_of_satisfiesScaledEssentialIdentity h hw huniq
    (isIntegralInvariantOnRestriction_of_mem_levelFixedVectors π ℓ v hv) hP hC⟩

end Essential

end Langlands.Conductor
