import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.Representation.Classification.SquareIntegrableEqualExponentGroupingProof
import Langlands.Representation.Classification.TemperedBlockUniquenessProof
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-!
# Square-integrable Langlands quotient classification

Equal-exponent grouping and regular tempered heads give strong head existence
and uniqueness for arbitrary irreducible quotients of each permitted datum.
Regular tempered data uniqueness then gives the complete classification by
finite permutations of actual square-integrable blocks.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every permitted square-integrable Langlands product has a strong
irreducible head, including when several chosen exponents coincide. -/
theorem squareIntegrableLanglandsHeadExistence :
    SquareIntegrableLanglandsHeadExistence.{uF, uV} F T := by
  let := T.topology
  intro n hn d
  obtain ⟨_, t, _, _, _, _, _, ⟨E⟩⟩ :=
    squareIntegrableEqualExponentGrouping.{uF, uV} F T n hn d
  obtain ⟨π, hπ⟩ := glRegularLanglandsHeadExistence.{uF, uV} p F T n hn t
  exact ⟨π, IsIrreducibleHead.of_equiv (SmoothRep.equivOfIso E).symm hπ⟩

/-- Any two actual irreducible quotients of the same permitted product
are isomorphic. Neither quotient witness needs to be a chosen head. -/
theorem squareIntegrableLanglandsQuotientUniqueness :
    SquareIntegrableLanglandsQuotientUniqueness.{uF, uV} F T := by
  let := T.topology
  intro n hn d π π' hπ hπ'
  obtain ⟨ρ, hρ⟩ := squareIntegrableLanglandsHeadExistence.{uF, uV} F T n hn d
  exact nonempty_iso_of_isIrreducibleHead hρ hπ hπ'

/-- Matching blocks, with their full multiplicities and the displayed rank
transports, give isomorphic arbitrary irreducible Langlands quotients. -/
theorem nonempty_iso_of_squareIntegrableLanglands_blockMatching
    {n : ℕ} (hn : 0 < n)
    (d d' : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    (π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : d.IsLanglandsQuotient π) (hπ' : d'.IsLanglandsQuotient π')
    (h : ∃ e : Fin d.shape.length ≃ Fin d'.shape.length,
      ∀ i, ∃ h : d.shape.size i = d'.shape.size (e i),
        Nonempty ((h ▸ d.blocks i) ≅ d'.blocks (e i))) :
    letI := T.topology
    Nonempty (π ≅ π') := by
  obtain ⟨e, H⟩ := h
  exact nonempty_iso_of_rankIso
    (squareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (temperedBlockUniqueness.{uF, uV} F T)
    glRegularLanglandsHeadExistence.{uF, uV} hn d d' hπ hπ' e H

/-- Irreducible quotients of permitted square-integrable Langlands products
are isomorphic exactly when their blocks match with multiplicities. -/
theorem squareIntegrableLanglandsClassification :
    SquareIntegrableLanglandsClassification.{uF, uV} F T :=
  squareIntegrableLanglandsClassification_of_regular.{uF, uV} F T
    (squareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (temperedBlockUniqueness.{uF, uV} F T)
    glRegularLanglandsHeadExistence.{uF, uV}
    glRegularLanglandsDataUniqueness.{uF, uV}

end Langlands.Classification
