import Langlands.Representation.Classification.SquareIntegrableUnitarityStatement
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Category.Contragredient
import Langlands.Group.GL.CentralQuotientUnimodularityProof

/-!
# Unitarizability of square-integrable p-adic GL representations

The generic coefficient-integral construction applies to the actual general
linear group, using compact-open cofinality and right invariance of Haar measure
on its full central quotient for the supplied field topology.
-/

namespace Langlands

universe uF uV

/-- An irreducible analytically square-integrable positive-rank p-adic GL
representation admits an invariant positive definite Hermitian form on its
original algebraic carrier. -/
theorem glSquareIntegrableUnitarity :
    GLSquareIntegrableUnitarityStatement.{uF,uV} := by
  intro p _ F T n hn V _ _ ρ hirr hsq
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearSecondCountableTopology n
  let := T.centralQuotientMeasurableSpace n
  let := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  let := hμ
  let := glCentralQuotientHaarRightInvariant p F T n hn μ
  exact squareIntegrableUnimodularUnitarity.{uF,uV}
    (GeneralLinear n F.Carrier) (GeneralLinear.compactOpen_cofinal F T n)
    V ρ μ hirr (hsq μ)

end Langlands
