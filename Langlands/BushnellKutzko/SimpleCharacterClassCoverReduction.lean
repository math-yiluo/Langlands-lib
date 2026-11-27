import Langlands.BushnellKutzko.ClassCoverFibreScalar

/-! # Reduction of the simple-character class cover (BK94 (2.3), upper half) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Pure-stratum approximation, conjugation, choice independence, restriction, coherence,
translation and covariance of simple characters imply the upper half of BK94 (2.3) in the form
of `SimpleCharacterClassCoverStatement`. For a nonarchimedean local field `F`, a
finite-dimensional `F`-vector space `V`, an additive character `ψ_F` trivial on `𝔭_F` and
nontrivial on `𝔬_F`, an indexed lattice chain `L` and integers `0 ≤ m < n`, there is one
function `Φ` on the simple strata `[𝔄,n,m,β]` on `L` such that `Φ` chooses a pair of each
stratum's own set `Ĉ(𝔄,m,β)`; `Φ` takes `U(𝔄)`-conjugate values on two strata whenever
`β' ≡ u⁻¹ β u (mod 𝔓^{-m})` for some `u ∈ U(𝔄)`; and every pair of `S^m_n(𝔄)`, the union of the
sets `Ĉ(𝔄,m,β)`, is `U(𝔄)`-conjugate to a value of `Φ`. -/
def SimpleCharacterClassCoverReductionStatement : Prop :=
  PureStratumSimpleApproximationStatement.{uF, uV} →
  SimpleCharacterConjugationStatement.{uF, uV} →
  SimpleCharacterChoiceStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterCoherenceStatement.{uF, uV} →
  SimpleCharacterTranslationStatement.{uF, uV} →
  SimpleCharacterCovarianceStatement.{uF, uV} →
  SimpleCharacterClassCoverStatement.{uF, uV}

/-- **BK94 (2.3), upper half,** from the seven statements of
`SimpleCharacterClassCoverReductionStatement`; the group properties of simple strata are the
Library's `simpleStratumGroupProperties`. -/
theorem simpleCharacterClassCoverReduction :
    SimpleCharacterClassCoverReductionStatement.{uF, uV} := by
  intro hApprox hConj hChoice hRestr hCoh hTransl hCov
  exact simpleCharacterClassCover_of_fibreCharacter hApprox hConj hChoice
    simpleStratumGroupProperties hRestr hCoh hTransl hCov (by
      intro F _ _ _ _ V _ _ _ ψF hψ L n k _
      exact fibreCharacterAt ψF hChoice hψ L n k)

end Langlands.BushnellKutzko
