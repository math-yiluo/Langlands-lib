import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.LocalField.LaurentSeries

/-!
# Close-fields comparison of torsion-number-one Weil orbit counts

The count form of the close-fields comparison: a p-adic field and the Laurent-series
field over its residue field have the same torsion-number-one Weil orbit counts below
the absolute ramification index.
-/

namespace Langlands.Henniart

/-- The count form of the close-fields comparison (E1a). For a p-adic field `K` with
absolute ramification index `e` and residue field `𝓀`, and `X = 𝓀((t))`, the
torsion-number-one Weil orbit counts `T_K(k + 1, s)` and `T_X(k + 1, s)` agree whenever
`s < (k + 1) * e`. -/
def CloseFieldsTwistCountStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uK} p) (k s : ℕ),
    s < (k + 1) * F.canonicalTopologicalData.ramificationIndex →
      letI : ValuativeRel (LaurentSeries (Weil.Local.localResidueField F)) :=
        LocalField.Laurent.valuativeRel (Weil.Local.localResidueField F)
      Numerical.weilTwistIrreducibleCount.{uK, uW} F k s =
        LocalNumerical.weilTwistIrreducibleCount.{uK, uK, uW}
          (LaurentSeries (Weil.Local.localResidueField F))
          (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))) k s

end Langlands.Henniart
