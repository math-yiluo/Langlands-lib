import Langlands.Automorphic.AssociatedGammaLocalLink
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Correspondence.AutomorphicGammaTransfer
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Representation.Twist.AlgebraProof

/-!
# Local pair data of a character twist

For a `p`-adic field `K`, classes `π`, `π'`, a quasi-character `η`, a nontrivial additive
character `ψ` and a self-dual measure `ν`, the twisted pair data are the L-polynomial of
`(π ⊗ η, π')`, the L-polynomial of the dual pair and the epsilon factor of `(π ⊗ η, π')`.
They always exist, and their gamma expression continues every certified gamma factor of
`(π ⊗ η, π')`.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- `d = (P, Pd, e)` are the pair L-polynomial of `(π ⊗ η, π')`, the pair L-polynomial of
the smooth duals, and the pair epsilon factor of `(π ⊗ η, π')`, at `ψ` and `ν`. -/
def IsTwistedPairData (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    {r t : ℕ} (π : AutomorphicClass.{u, u} K r.succPNat)
    (π' : AutomorphicClass.{u, u} K t.succPNat) (η : QuasiCharacter K)
    (d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)) : Prop :=
  ∃ (πη πd : AutomorphicClass.{u, u} K r.succPNat) (πd' : AutomorphicClass.{u, u} K t.succPNat),
    IsCharacterTwist K η π πη ∧ IsSmoothDual K πη πd ∧ IsSmoothDual K π' πd' ∧
      IsAutomorphicPairLPolynomial K ψ ν πη π' d.1 ∧
      IsAutomorphicPairLPolynomial K ψ ν πd πd' d.2.1 ∧
      IsAutomorphicPairEpsilonFactor K ψ ν πη π' d.2.2

variable {K}

/-- A character twist of a class is unique. -/
theorem IsCharacterTwist.unique {n : ℕ+} {η : QuasiCharacter K}
    {π π₁ π₂ : AutomorphicClass.{u, u} K n}
    (h₁ : IsCharacterTwist K η π π₁) (h₂ : IsCharacterTwist K η π π₂) : π₁ = π₂ := by
  have hopen := isOpen_ker_determinantQuasiCharacter K n η
  rw [(isCharacterTwist_iff_eq_twist K η hopen π π₁).mp h₁,
    (isCharacterTwist_iff_eq_twist K η hopen π π₂).mp h₂]

/-- A smooth dual of a class is unique. -/
theorem IsSmoothDual.unique {n : ℕ+} {π π₁ π₂ : AutomorphicClass.{u, u} K n}
    (h₁ : IsSmoothDual K π π₁) (h₂ : IsSmoothDual K π π₂) : π₁ = π₂ := by
  rw [(isSmoothDual_iff_eq_contragredient K π π₁).mp h₁,
    (isSmoothDual_iff_eq_contragredient K π π₂).mp h₂]

/-- Every class is its own twist by the trivial character. -/
theorem isCharacterTwist_one {n : ℕ+} (π : AutomorphicClass.{u, u} K n) :
    IsCharacterTwist K 1 π π := by
  obtain ⟨A, rfl⟩ := automorphicClass_has_representative K π
  refine ⟨A, A, rfl, rfl, ?_⟩
  have h1 : determinantQuasiCharacter K n (1 : QuasiCharacter K) = 1 := by
    ext g
    rfl
  rw [h1, Langlands.twist_one]
  exact ⟨Representation.Equiv.refl _⟩

/-- Twisted pair data exist for every self-dual measure. -/
theorem exists_isTwistedPairData (ψ : NontrivialAdditiveCharacter K)
    {ν : LocalAdditiveHaarMeasure K} (hν : IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (π : AutomorphicClass.{u, u} K r.succPNat) (π' : AutomorphicClass.{u, u} K t.succPNat)
    (η : QuasiCharacter K) : ∃ d, IsTwistedPairData K ψ ν π π' η d := by
  have hopen := isOpen_ker_determinantQuasiCharacter K r.succPNat η
  obtain ⟨πη, htw⟩ : ∃ πη, IsCharacterTwist K η π πη :=
    ⟨_, (isCharacterTwist_iff_eq_twist K η hopen π _).mpr rfl⟩
  obtain ⟨πd, hd⟩ : ∃ πd, IsSmoothDual K πη πd :=
    ⟨_, (isSmoothDual_iff_eq_contragredient K πη _).mpr rfl⟩
  obtain ⟨πd', hd'⟩ : ∃ πd', IsSmoothDual K π' πd' :=
    ⟨_, (isSmoothDual_iff_eq_contragredient K π' _).mpr rfl⟩
  obtain ⟨P, hP⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    K ψ hν πη π'
  obtain ⟨Pd, hPd⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    K ψ hν πd πd'
  obtain ⟨e, he⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairEpsilonFactor
    K ψ hν πη π'
  exact ⟨(P, Pd, e), πη, πd, πd', htw, hd, hd', hP, hPd, he⟩

/-- Twisted pair data are the factors of any twist and any smooth duals. -/
theorem IsTwistedPairData.specs {ψ : NontrivialAdditiveCharacter K}
    {ν : LocalAdditiveHaarMeasure K} {r t : ℕ}
    {π : AutomorphicClass.{u, u} K r.succPNat} {π' : AutomorphicClass.{u, u} K t.succPNat}
    {η : QuasiCharacter K} {d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)}
    (hd : IsTwistedPairData K ψ ν π π' η d)
    {πη πd : AutomorphicClass.{u, u} K r.succPNat} {πd' : AutomorphicClass.{u, u} K t.succPNat}
    (htw : IsCharacterTwist K η π πη) (hdual : IsSmoothDual K πη πd)
    (hdual' : IsSmoothDual K π' πd') :
    IsAutomorphicPairLPolynomial K ψ ν πη π' d.1 ∧
      IsAutomorphicPairLPolynomial K ψ ν πd πd' d.2.1 ∧
      IsAutomorphicPairEpsilonFactor K ψ ν πη π' d.2.2 := by
  obtain ⟨πη₀, πd₀, πd₀', htw₀, hdual₀, hdual₀', hP, hPd, he⟩ := hd
  obtain rfl : πη₀ = πη := htw₀.unique htw
  obtain rfl : πd₀ = πd := hdual₀.unique hdual
  obtain rfl : πd₀' = πd' := hdual₀'.unique hdual'
  exact ⟨hP, hPd, he⟩

open Classical in
/-- A choice of twisted pair data. -/
def twistedPairData (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    {r t : ℕ} (π : AutomorphicClass.{u, u} K r.succPNat)
    (π' : AutomorphicClass.{u, u} K t.succPNat) (η : QuasiCharacter K) :
    ℂ[X] × ℂ[X] × (ℂˣ × ℤ) :=
  Classical.epsilon (IsTwistedPairData K ψ ν π π' η)

theorem twistedPairData_spec (ψ : NontrivialAdditiveCharacter K)
    {ν : LocalAdditiveHaarMeasure K} (hν : IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (π : AutomorphicClass.{u, u} K r.succPNat) (π' : AutomorphicClass.{u, u} K t.succPNat)
    (η : QuasiCharacter K) :
    IsTwistedPairData K ψ ν π π' η (twistedPairData ψ ν π π' η) :=
  Classical.epsilon_spec (exists_isTwistedPairData ψ hν π π' η)

end Langlands.Correspondence

namespace Langlands.Global.FunctionalEquationComparison

open Langlands.Correspondence

/-- The local factors `1 / P(q^-s)`, `1 / Pd(q^-s)`, `c q^(-m s)` of pair data. -/
def pairDataFactors (q : ℕ) (d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)) : LocalFactors :=
  ⟨fun s => (d.1.eval (RankinSelberg.spectralPoint q s))⁻¹,
    fun s => (d.2.1.eval (RankinSelberg.spectralPoint q s))⁻¹,
    fun s => (d.2.2.1 : ℂ) * RankinSelberg.spectralPoint q s ^ d.2.2.2⟩

theorem pairDataFactors_gamma (q : ℕ) (d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)) :
    (pairDataFactors q d).gamma =
      RankinSelberg.polynomialGammaExpression q d.2.2.1 d.2.2.2 d.1 d.2.1 := rfl

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

/-- The gamma factor of twisted pair data continues every certified gamma factor of the
twisted pair. -/
theorem hasRationalContinuation_pairDataFactors_gamma
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K} {r t : ℕ}
    {π : AutomorphicClass.{u, u} K r.succPNat} {π' : AutomorphicClass.{u, u} K t.succPNat}
    {η : QuasiCharacter K} {d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)}
    (hd : IsTwistedPairData K ψ ν π π' η d)
    {πη : AutomorphicClass.{u, u} K r.succPNat} (hπη : IsCharacterTwist K η π πη)
    {G : RatFunc ℂ} (hG : IsAutomorphicPairGammaFactor K ψ ν πη π' G) :
    RankinSelberg.HasRationalContinuation K.canonicalTopologicalData.residueCardinality
      (pairDataFactors K.canonicalTopologicalData.residueCardinality d).gamma G := by
  obtain ⟨πη₀, πd, πd', htw, hdual, hdual', hP, hPd, he⟩ := hd
  have hη : πη₀ = πη := htw.unique hπη
  subst hη
  have hGeq : G = RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K)
      d.2.2.1 d.2.2.2 d.1 d.2.1 :=
    hG.unique (automorphicPairGammaFactor hdual hdual' hP hPd he).property
  have hPd0 : d.2.1 ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hL⟩ := hPd
    exact hL.ne_zero
  rw [pairDataFactors_gamma, hGeq]
  exact RankinSelberg.hasRationalContinuation_polynomialGammaExpression
    K.canonicalTopologicalData.residueCardinality_gt_one
    (LocalFactor.coe_residueReflection K) _ _ _ _ hPd0

/-- Twisted pair data give a certified gamma factor of the twisted pair. -/
theorem IsTwistedPairData.exists_gamma
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K} {r t : ℕ}
    {π : AutomorphicClass.{u, u} K r.succPNat} {π' : AutomorphicClass.{u, u} K t.succPNat}
    {η : QuasiCharacter K} {d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)}
    (hd : IsTwistedPairData K ψ ν π π' η d) :
    ∃ πη : AutomorphicClass.{u, u} K r.succPNat, IsCharacterTwist K η π πη ∧
      IsAutomorphicPairGammaFactor K ψ ν πη π'
        (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K)
          d.2.2.1 d.2.2.2 d.1 d.2.1) := by
  obtain ⟨πη, πd, πd', htw, hdual, hdual', hP, hPd, he⟩ := hd
  exact ⟨πη, htw, (automorphicPairGammaFactor hdual hdual' hP hPd he).property⟩

end Langlands.Global.FunctionalEquationComparison
