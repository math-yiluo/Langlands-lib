import Langlands.Representation.Classification.SpehLanglandsAdapters
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof

/-! Actual existence and uniqueness of the centered Speh quotient. -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every discrete-series datum has an actual centered Speh quotient, unique
up to isomorphism among all irreducible smooth quotients. -/
theorem spehExistenceUniqueness :
    SpehExistenceUniqueness.{uF, uV} F T := by
  let := T.topology
  intro d hd
  obtain ⟨π, hπ⟩ := glRegularLanglandsHeadExistence.{uF, uV}
    p F T d.degree d.degree_pos (d.temperedLanglandsDatum hd)
  exact ⟨π, d.isSpeh_of_isLanglandsHead hd hπ⟩

end Langlands.Classification
