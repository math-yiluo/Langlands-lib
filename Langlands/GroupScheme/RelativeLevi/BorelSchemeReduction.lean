import Langlands.GroupScheme.RelativeLevi.BorelSchemeStatement
import Langlands.GroupScheme.RelativeLevi.ParabolicSchemeStatement
import Langlands.GroupScheme.RelativeLevi.BorelRepresentation
import Langlands.GroupScheme.RelativeLevi.BorelLocusProof

/-! # Borel representability from parabolic representability and the clopen locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open RelativeLevi

/-- The exact Borel-scheme statement follows from the exact parabolic-scheme
statement and the exact clopen Borel-locus statement. -/
theorem relativeBorelScheme_of_parabolicScheme_and_borelLocus
    (hpar : RelativeParabolicSchemeStatement.{u})
    (hcl : RelativeBorelLocusClopenStatement.{u}) :
    RelativeBorelSchemeStatement.{u} := by
  intro S G hG
  obtain ⟨M, P, j, hj, huni, hsm, hproper⟩ := hpar S G hG
  let : Smooth M.hom := hsm
  let : IsProper M.hom := hproper
  let d := borelSchemeDataOfParabolic hcl hG j hj huni
  exact ⟨d.parameter, d.group, d.inclusion, d.isBorel, d.universal, d.smooth, d.proper⟩

/-- Parabolic representability suffices for Borel representability, using the
published unconditional clopen-locus theorem. -/
theorem relativeBorelScheme_of_parabolicScheme
    (hpar : RelativeParabolicSchemeStatement.{u}) :
    RelativeBorelSchemeStatement.{u} :=
  relativeBorelScheme_of_parabolicScheme_and_borelLocus hpar relativeBorelLocusClopen

end Langlands.GroupScheme
