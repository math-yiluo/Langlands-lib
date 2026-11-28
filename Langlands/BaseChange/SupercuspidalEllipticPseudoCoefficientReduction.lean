import Langlands.BaseChange.SupercuspidalEllipticPseudoCoefficientStatement
import Langlands.BaseChange.CuspFormOrbitalVanishingStatement
import Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient

/-!
# Elliptic pseudo-coefficients of supercuspidal representations from cusp-form descent

`SupercuspidalEllipticPseudoCoefficientReductionStatement` is the implication
`CuspFormOrbitalVanishingStatement → SupercuspidalEllipticPseudoCoefficientStatement`, and
`supercuspidalEllipticPseudoCoefficientReduction` proves it: the cut-off supercuspidal
coefficient of `SupercuspidalCutoff.exists_cuspForm_pseudoCoefficient` has vanishing constant
terms, trace `1` on `π` and trace `0` on every other irreducible admissible representation with
the central character of `π`, and `CuspFormOrbitalVanishingStatement` turns its vanishing
constant terms into the vanishing of its orbital integrals off the elliptic set. See the paired
Markdown.
-/

namespace Langlands.BaseChange

/-- The orbital-integral descent for cusp forms (`CuspFormOrbitalVanishingStatement`) implies
the existence of elliptic pseudo-coefficients of supercuspidal representations of `GL_n`
(`SupercuspidalEllipticPseudoCoefficientStatement`), at the same field universe `u` and for
all carrier universes `uV`, `uW`. -/
def SupercuspidalEllipticPseudoCoefficientReductionStatement.{u, uV, uW} : Prop :=
  CuspFormOrbitalVanishingStatement.{u} →
    SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW}

/-- **Reduction to cusp-form descent.** -/
theorem supercuspidalEllipticPseudoCoefficientReduction.{u, uV, uW} :
    SupercuspidalEllipticPseudoCoefficientReductionStatement.{u, uV, uW} := by
  intro hvan F _ _ _ _ _ n hn
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  intro V _ _ π hπ hirr χ hχ μ _
  obtain ⟨f, hcusp, h1, h0⟩ :=
    SupercuspidalCutoff.exists_cuspForm_pseudoCoefficient.{u, uV, uW} μ hn π hπ hirr hχ
  exact ⟨f, hvan F n hn μ f hcusp, h1, h0⟩

end Langlands.BaseChange
