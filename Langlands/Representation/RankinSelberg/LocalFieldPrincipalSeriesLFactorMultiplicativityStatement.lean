import Langlands.Representation.RankinSelberg.GeneralPairLFactor
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# L-factor multiplicativity for unramified principal series over every local field

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (3.1)(ii) (printed pages 404–405),
over an arbitrary nonarchimedean local field `F` (any characteristic), for the
second representation an unramified principal series
`I(z) = Ind(χ_{z_0}, …, χ_{z_n})` of `GL_(n+1)(F)`: the L-polynomials of `π × I(z)` and
of every `π × χ_{z_i}` exist, and `L(s, π × I(z))` lies in
`∏ i, L(s, π × χ_{z_i}) ℂ[q^(-s), q^s]`. The hypotheses are those of
`LocalFieldPrincipalSeriesGammaMultiplicativityStatement`, the companion statement of
part (i). The induction is from the upper triangular Borel subgroup; the source
induces from the lower one, and the two agree after reversing `z` (see the Markdown).
This module contains no proof.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- JPSS 1983, Theorem (3.1)(ii) (printed page 405), for `σ = I(z)` an unramified
principal series, over every nonarchimedean local field `F`. `q` is the residue
cardinality, `ϖ` a uniformizer and `abv` the normalized absolute value
(`abv ϖ = q⁻¹`, `abv x = 1` on valuation units); `ν` is self-dual for `ψ`. For every
representation `π` of `GL_(r+1)(F)` of Whittaker type for the standard character and
every `z : Fin (n + 1) → ℂˣ`, the pair `(π, I(z))` has an L-polynomial `P`, each pair
`(π, χ_{z_i})` has an L-polynomial `Pi i`, and `X ^ e * ∏ i, Pi i = Q * P` for a
polynomial `Q` and some `e : ℕ`, that is,
`L(s, π × I(z)) ∈ ∏ i, L(s, π × χ_{z_i}) ℂ[q^(-s), q^s]` with `X = q^(-s)`. All
relations are the larger-rank-first relation `IsGeneralSymmetricLPolynomial`. -/
def LocalFieldPrincipalSeriesLFactorMultiplicativityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F],
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (q : ℕ) (hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality (F := F) q)
    (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ),
    abv (ϖ : F) = (q : ℝ)⁻¹ → (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
  ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
  ∀ (r n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
    IsOfWhittakerType r (standardCharacter ψ r) π →
  ∀ z : Fin (n + 1) → ℂˣ,
    ∃ (P : ℂ[X]) (Pi : Fin (n + 1) → ℂ[X]),
      IsGeneralSymmetricLPolynomial q ψ abv ν π
        (Conductor.UnramifiedPrincipalSeries.principalSeries hϖ n hq z) P ∧
      (∀ i, IsGeneralSymmetricLPolynomial q ψ abv ν π
        (rankOneCharacter (Conductor.UnramifiedPrincipalSeries.character hϖ (z i))) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

end Langlands.RankinSelberg
