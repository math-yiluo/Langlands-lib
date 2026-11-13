import Langlands.Representation.RankinSelberg.GeneralPairGamma
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# Gamma multiplicativity for unramified principal series over every local field

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (3.1)(i) (printed pages 404–405),
over an arbitrary nonarchimedean local field `F` (any characteristic), for the
second representation an unramified principal series
`I(z) = Ind(χ_{z_0}, …, χ_{z_n})` of `GL_(n+1)(F)`. Here `χ_z` is the unramified
character of `Fˣ` with `χ_z(ϖ) = z`, and the induction is the published normalized
induction `Conductor.UnramifiedPrincipalSeries.principalSeries` from the upper
triangular Borel subgroup. The source induces from the lower Borel subgroup; the two
inductions are isomorphic after reversing the tuple `z`, and the product of the gamma
factors does not depend on the order (see the Markdown). This module contains no proof.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- JPSS 1983, Theorem (3.1)(i) (printed page 405), for `σ = I(z)` an unramified
principal series, over every nonarchimedean local field `F`. `q` is the residue
cardinality, `ϖ` a uniformizer and `abv` the normalized absolute value
(`abv ϖ = q⁻¹`, `abv x = 1` on valuation units); `ν` is self-dual for `ψ`. For every
representation `π` of `GL_(r+1)(F)` of Whittaker type for the standard character and
every `z : Fin (n + 1) → ℂˣ`, each pair `(π, χ_{z_i})` has a gamma factor `G i`, and
`∏ i, G i` is the gamma factor of `(π, I(z))`. Both relations are the
larger-rank-first relation `IsGeneralSymmetricGammaFactor`. -/
def LocalFieldPrincipalSeriesGammaMultiplicativityStatement : Prop :=
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
    ∃ G : Fin (n + 1) → RationalFunctions,
      (∀ i, IsGeneralSymmetricGammaFactor q ψ abv ν π
        (rankOneCharacter (Conductor.UnramifiedPrincipalSeries.character hϖ (z i))) (G i)) ∧
      IsGeneralSymmetricGammaFactor q ψ abv ν π
        (Conductor.UnramifiedPrincipalSeries.principalSeries hϖ n hq z) (∏ i, G i)

end Langlands.RankinSelberg
