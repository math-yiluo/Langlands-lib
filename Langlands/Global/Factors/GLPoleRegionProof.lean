import Langlands.Global.Factors.GLPoleRegionTempered
import Langlands.Global.Factors.GLPoleRegionSmallSupercuspidal

/-!
# Proof of the GL pole-region statement

`GLPairPoleRegionStatement`: the `GL_n` half of Henniart 1986, Proposition 4.5(ii),
for JPSS L-polynomials. Every realization is replaced by the canonical one, the two
L-polynomials of the statement are identified with the p-adic pair L-polynomials of
`(π, σ)` for `ψ` and of `(π^ι, σ^ι)` for `ψ⁻¹`, and each case of the hypothesis is
handled by its own lemma.
-/

noncomputable section

namespace Langlands.Global

universe uF uV uW

open GLPoleRegion

/-- **Henniart 1986, Proposition 4.5(ii), `GL_n` side**: over every p-adic field and
realization, in equal and in unequal ranks, the JPSS L-polynomial `P_{π × σ}` and the
reflected `P_{π^ι × σ^ι}` have no common zero whenever `π` and `σ` are both
essentially tempered or one of them (in equal rank: `σ`) is supercuspidal. -/
theorem glPairPoleRegion : GLPairPoleRegionStatement.{uF, uV, uW} := by
  intro p _ F T
  obtain rfl := T.eq_canonicalTopologicalData
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  refine ⟨fun n => ?_, fun n j k => ?_⟩
  · intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ hcase P Pd hP hPd
    obtain ⟨ν⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar F ψ
    obtain ⟨νd⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar F (ψ.scale (-1))
    rcases hcase with ⟨heπ, heσ⟩ | hscσ
    · obtain ⟨hP', hPd'⟩ :=
        isPadicPairLPolynomial_of_equalRank ν.val νd.val hπ hσ μ hμ P Pd hP hPd
      exact hasNoReflectedCommonZero_of_essentiallyTempered ν νd le_rfl hπ.1 hσ.1 heπ heσ
        hP' hPd'
    · obtain ⟨hP', hPd'⟩ :=
        isPadicPairLPolynomial_of_equalRank ν.val ν.val hπ hσ μ hμ P Pd hP hPd
      exact hasNoReflectedCommonZero_of_supercuspidal_equalRank ν hπ.1 hσ.1 hscσ
        (RankinSelberg.isOfWhittakerType_of_isGeneric F hπ)
        (isOfWhittakerType_of_scale_neg_one ψ
          (RankinSelberg.isOfWhittakerType_of_isGeneric F hσ)) hP' hPd'
  · intro ψ _ μ hμ ν₀ V _ _ W _ _ π σ hπ hσ hcase P Pd hP hPd
    obtain ⟨ν⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar F ψ
    obtain ⟨νd⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar F (ψ.scale (-1))
    rcases hcase with ⟨heπ, heσ⟩ | hscσ | hscπ
    · obtain ⟨hP', hPd'⟩ :=
        isPadicPairLPolynomial_of_unequalRank ν.val νd.val hπ hσ μ hμ ν₀ P Pd hP hPd
      exact hasNoReflectedCommonZero_of_essentiallyTempered ν νd (by omega) hπ.1 hσ.1
        heπ heσ hP' hPd'
    · obtain ⟨hP', hPd'⟩ :=
        isPadicPairLPolynomial_of_unequalRank ν.val ν.val hπ hσ μ hμ ν₀ P Pd hP hPd
      exact hasNoReflectedCommonZero_of_supercuspidal_le ν (by omega) hπ hσ.1 hscσ hP' hPd'
    · obtain ⟨hP', -⟩ :=
        isPadicPairLPolynomial_of_unequalRank ν.val ν.val hπ hσ μ hμ ν₀ P Pd hP hPd
      exact hasNoReflectedCommonZero_of_supercuspidal_unequalRank ν (by omega) hπ.1 hscπ
        (isOfWhittakerType_of_scale_neg_one ψ
          (RankinSelberg.isOfWhittakerType_of_isGeneric F hσ)) hP'

end Langlands.Global
