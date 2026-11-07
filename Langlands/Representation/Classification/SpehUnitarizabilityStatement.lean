import Langlands.Representation.Classification.TadicUnitaryStatement

/-!
# Unitarizability of Speh representations

Tadic 1986, Appendix, Theorem A.8: every Speh representation `u(delta,k)`
of `GL_(k r)` over a p-adic field is unitarizable. The assertion is a
proposition definition over the published Speh relation; it assumes neither
existence of the Speh quotient nor any classification result.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadic 1986 Appendix, Theorem A.8: for discrete-series data `d`, every
actual smooth representation `pi` of `GL_(k r)` satisfying `d.IsSpeh pi`,
that is, every representative of `u(delta,k)`, admits an invariant positive
definite Hermitian form. No Speh quotient is assumed to exist. -/
def SpehUnitarizability : Prop :=
  letI := T.topology
  ∀ d : SpehDatum.{uF, uV} F T, d.IsDiscreteSeries →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier),
      d.IsSpeh π → IsUnitarizable π.representation

end Langlands.Classification
