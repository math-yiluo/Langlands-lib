import Langlands.Representation.Conductor.Essential

/-!
# Integral last-row support of the essential vector

Jacquet, Piatetski-Shapiro and Shalika 1981, Section (5.2), the lemma on printed
page 212: if `W` is the essential vector of `π` on `GL_r(F)` and
`W(diag(g, 1)) ≠ 0` with `g ∈ GL_(r-1)(F)`, then the last row of `g` has integral
entries. The essential vector is the corrected one of Jacquet 2012, Theorem 1, as
defined by the published `IsEssentialVector`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV

/-- JPSS 1981, Section (5.2), lemma on printed page 212, in rank `r = n + 2`. Under
Jacquet's normalizations `h`, for an irreducible admissible generic representation `π`
of `GL_(n+2)(F)`, a nonzero `ψ`-Whittaker functional `ℓ` and an essential vector `w`
of its model, every `g ∈ GL_(n+1)(F)` with `w(diag(g, 1)) ≠ 0` has its last row in
`O^(n+1)`, where `O` is the valuation ring of `F`. -/
def EssentialIntegralLastRowSupportStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
    IsGeneric ψ (n + 1) π →
    ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
    ∀ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w →
    ∀ g : Langlands.GeneralLinear (n + 1) F,
      w.val.val (rankInclusion 1 g) ≠ 0 →
      ∀ j : Fin (n + 1), g.val (Fin.last n) j ∈ (ValuativeRel.valuation F).integer

end Langlands.Conductor
