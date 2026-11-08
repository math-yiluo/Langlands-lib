import Langlands.Representation.RankinSelberg.HighlyRamified.KirillovShell
import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.Whittaker.CompletenessStatement
import Langlands.Representation.RankinSelberg.UniformRankOneTwistStatement
import Langlands.Representation.RankinSelberg.HighlyRamifiedStatement

/-!
# Highly ramified gamma stability from its published prerequisites

The adjacent-rank step and the induction of Jacquet–Shalika 1985, §4, reduce
`HighlyRamifiedGammaStabilityStatement` to three published statements: the completeness of
Whittaker functions (JS85 Lemma (3.2)), the essential-vector and conductor theorems
(Jacquet 2012, JPSS 1981 Théorème (5.1)) and the level-uniform rank-one stability
(JS85 Proposition (2.2)). The Kirillov shell input is proved in
`HighlyRamified.KirillovShell`.
-/

namespace Langlands.RankinSelberg.HighlyRamified

universe uF uV uW

/-- Full generic pair gamma stability from the three published prerequisite statements. -/
theorem highlyRamifiedGammaStability_of_prerequisites
    (hT1 : Whittaker.WhittakerCompletenessStatement.{uF, max uF uV uW})
    (h2 : Conductor.EssentialConductorStatement.{uF, max uF uV uW})
    (h3 : UniformRankOneTwistStatement.{uF, max uF uV uW})
    (hone : UniformRankOneTwistStatement.{uF, uV}) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_inputs hT1 h2.2.2 h3 hone kirillovShellInput

end Langlands.RankinSelberg.HighlyRamified
