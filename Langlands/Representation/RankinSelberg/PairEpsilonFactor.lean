import Langlands.Representation.RankinSelberg.EpsilonFactor

/-! Conditional epsilon factors chosen from the published JPSS relation. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW uV₂ uW₂

/-- The nonzero rational monomial `c X^m` in the JPSS spectral variable. -/
def rationalEpsilonMonomial (c : ℂˣ) (m : ℤ) : RationalFunctionsˣ :=
  Units.map (algebraMap ℂ RationalFunctions) c *
    (Units.mk0 (RatFunc.X : RationalFunctions) RatFunc.X_ne_zero) ^ m

@[simp]
theorem coe_rationalEpsilonMonomial (c : ℂˣ) (m : ℤ) :
    (rationalEpsilonMonomial c m : RationalFunctions) =
      algebraMap ℂ RationalFunctions (c : ℂ) * RatFunc.X ^ m := by
  simp [rationalEpsilonMonomial]

section Pair

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

/-- There is a monomial satisfying the pair epsilon-factor relation. -/
def PairEpsilonFactorExists (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) : Prop :=
  ∃ e : ℂˣ × ℤ, IsPairEpsilonFactor q ψ abv ν π σ e

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- The coefficient and exponent, chosen from an existence proof. -/
def pairEpsilonData (h : PairEpsilonFactorExists q ψ abv ν π σ) : ℂˣ × ℤ :=
  h.choose

theorem pairEpsilonData_spec (h : PairEpsilonFactorExists q ψ abv ν π σ) :
    IsPairEpsilonFactor q ψ abv ν π σ (pairEpsilonData h) :=
  h.choose_spec

theorem pairEpsilonData_eq (hq : 1 < q)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) {e : ℂˣ × ℤ}
    (he : IsPairEpsilonFactor q ψ abv ν π σ e) : pairEpsilonData h = e :=
  (pairEpsilonData_spec h).unique hq he

/-- Transport of epsilon existence along actual representation equivalences. -/
theorem PairEpsilonFactorExists.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) :
    PairEpsilonFactorExists q ψ abv ν π₂ σ₂ :=
  ⟨pairEpsilonData h, (pairEpsilonData_spec h).of_equiv φ φ'⟩

/-- Epsilon data are intrinsic to the representations up to equivalence. -/
theorem pairEpsilonData_congr_equiv (hq : 1 < q) (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : PairEpsilonFactorExists q ψ abv ν π σ)
    (h₂ : PairEpsilonFactorExists q ψ abv ν π₂ σ₂) :
    pairEpsilonData h = pairEpsilonData h₂ :=
  ((pairEpsilonData_spec h).of_equiv φ φ').unique hq (pairEpsilonData_spec h₂)

variable [BorelSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The epsilon factor as a unit rational function. The self-dual measure
hypothesis fixes the JPSS normalization. -/
def pairEpsilonFactor (_hν : IsSelfDual ψ ν)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) : RationalFunctionsˣ :=
  rationalEpsilonMonomial (pairEpsilonData h).1 (pairEpsilonData h).2

@[simp]
theorem coe_pairEpsilonFactor (hν : IsSelfDual ψ ν)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) :
    (pairEpsilonFactor hν h : RationalFunctions) =
      algebraMap ℂ RationalFunctions ((pairEpsilonData h).1 : ℂ) *
        RatFunc.X ^ (pairEpsilonData h).2 :=
  coe_rationalEpsilonMonomial _ _

theorem pairEpsilonFactor_eq (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) {e : ℂˣ × ℤ}
    (he : IsPairEpsilonFactor q ψ abv ν π σ e) :
    pairEpsilonFactor hν h = rationalEpsilonMonomial e.1 e.2 := by
  unfold pairEpsilonFactor
  rw [pairEpsilonData_eq hq h he]

theorem pairEpsilonFactor_congr_equiv (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : PairEpsilonFactorExists q ψ abv ν π σ)
    (h₂ : PairEpsilonFactorExists q ψ abv ν π₂ σ₂) :
    pairEpsilonFactor hν h = pairEpsilonFactor hν h₂ := by
  unfold pairEpsilonFactor
  rw [pairEpsilonData_congr_equiv hq φ φ' h h₂]

/-- The everywhere nonzero spectral epsilon monomial. -/
def pairEpsilonValue (hq : 1 < q) (_hν : IsSelfDual ψ ν)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) (s : ℂ) : ℂˣ :=
  Units.mk0 (epsilonMonomial q (pairEpsilonData h).1 (pairEpsilonData h).2 s)
    (epsilonMonomial_ne_zero q (by exact_mod_cast (show 0 < q by omega)) _ _ s)

@[simp]
theorem coe_pairEpsilonValue (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (h : PairEpsilonFactorExists q ψ abv ν π σ) (s : ℂ) :
    (pairEpsilonValue hq hν h s : ℂ) =
      epsilonMonomial q (pairEpsilonData h).1 (pairEpsilonData h).2 s := rfl

end Pair

end Langlands.RankinSelberg
