import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
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

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW uV₂ uW₂

section GammaEquation

end GammaEquation

section EqualRankEquation



end EqualRankEquation

section UnequalRankEquation



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

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {G G' : RationalFunctions}

section EqualRank


end EqualRank

section UnequalRank


end UnequalRank

section Pair


end Pair

end Relations

section Padic


/-- The gamma-factor relation for actual representations of `GL_(r+1)(F)` and
`GL_(n+1)(F)` over a p-adic field with its canonical topological data: `q` is
the residue cardinality and the absolute value is the normalized one. -/
def IsPadicPairGammaFactor (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  IsPairGammaFactor (⟨⟩ : LocalFieldData F).residueCardinality ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) ν π σ G

/-- The p-adic gamma factor is unique. -/
theorem IsPadicPairGammaFactor.unique {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : letI := borel F
      AdditiveHaarMeasure F}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {G G' : RationalFunctions} (h : IsPadicPairGammaFactor F ψ ν π σ G)
    (h' : IsPadicPairGammaFactor F ψ ν π σ G') : G = G' := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  exact IsPairGammaFactor.unique (Langlands.LocalFieldData.residueCardinality_gt_one _) h h'

/-- The p-adic gamma-factor relation is invariant under representation
equivalences. -/
theorem IsPadicPairGammaFactor.congr_equiv {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : letI := borel F
      AdditiveHaarMeasure F}
    {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {G : RationalFunctions} :
    IsPadicPairGammaFactor F ψ ν π σ G ↔ IsPadicPairGammaFactor F ψ ν π₂ σ₂ G := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  exact IsPairGammaFactor.congr_equiv φ φ'

end Padic

end Langlands.AllField.RankinSelberg
