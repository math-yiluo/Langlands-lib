import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement
import Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction

/-!
# Proof of gamma multiplicativity for unramified principal series over every local field

The all-field multiplicativity theorem `AllField.RankinSelberg.gammaMultiplicativity`,
applied to `n + 1` blocks of size one and the rank-one characters `χ_{z_0}, …, χ_{z_n}`,
gives the gamma factors of the pairs `(π, χ_{z_i})` and the gamma factor of `π` against
their normalized product induction. The latter is equivalent to `I(z)`
(`AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv`), and the hypothesized
`q` and `abv` are the residue cardinality and normalized absolute value of the ambient
local-field data.
-/

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

/-- JPSS 1983, Theorem (3.1)(i), for the unramified principal series `I(z)` over every
nonarchimedean local field. -/
theorem localFieldPrincipalSeriesGammaMultiplicativity :
    LocalFieldPrincipalSeriesGammaMultiplicativityStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ q hq abv ϖ hϖ habv hunit ψ ν hν r n V _ _ π hπ z
  have habvT := AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ
    habv hunit
  subst habvT
  have hqT : q = (LocalFieldData.ofInstances F).residueCardinality :=
    hq.trans AllField.RankinSelberg.residueCardinality_ofInstances.symm
  obtain ⟨G, hG, hGind⟩ := AllField.RankinSelberg.gammaMultiplicativity.{uF, uV, 0} F ψ
    ⟨ν, hν⟩ r n (n + 1) (fun _ => 0) (by simp) π
    (AllField.Conductor.UnramifiedPrincipalSeries.blocks hϖ n z) hπ
    (fun i => AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType F ψ
      (AllField.Conductor.UnramifiedPrincipalSeries.quasicharacter hϖ (z i)))
  refine ⟨G, fun i => ?_, ?_⟩
  · rw [hqT]
    exact hG i
  · rw [IsGeneralSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π)
      (AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv hϖ n hq z), hqT]
    exact hGind

end Langlands.RankinSelberg
