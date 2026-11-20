import Langlands.GroupScheme.RelativeLevi.AffineExistenceStatement
import Langlands.GroupScheme.RelativeLevi.TorsorProof
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalProof
import Langlands.GroupScheme.RelativeUnipotent.AffineTorsorProof
import Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationProof

/-! # Levi subgroups over affine bases -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A relative parabolic subgroup of a reductive group scheme over an affine
base has a Levi subgroup. -/
theorem relativeLeviAffineExistence : RelativeLeviAffineExistenceStatement.{u} := by
  intro S _ G P i hG hP
  obtain ⟨U, r, hU, _⟩ := relativeUnipotentRadical S G P i hG hP
  let : Smooth U.X.hom := hU.smooth
  let : IsAffineHom P.X.hom := hP.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hU.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have hseries := relativeUnipotentRadicalFiltration S G P U i r hG hP hU
  obtain ⟨X, action, ρ, _, hflat, hsurj, hqc, hiso⟩ :=
    relativeLeviTorsor S G P U i r hG hP hU
  let : ModObj U.X X := action
  obtain ⟨s, hs⟩ := relativeUnipotentAffineTorsor S U hseries X hflat hsurj hqc hiso
  exact ρ.exists_isRelativeLeviSubgroup_of_section s hs

end Langlands.GroupScheme
