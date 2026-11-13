import Langlands.BruhatTits.SpecialCompact.AvailableBasisStatement
import Langlands.BruhatTits.SpecialCompact.CompatibleApartmentProperties
import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly

/-! # The simultaneous basis at every special vertex of valid corrected KP data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- Renard V.5.1–V.5.2 at every special apartment vertex of a valid corrected KP
assignment: compact properties, geometric Levi inheritance and the simultaneous
standard basis, for the same datum, torus, cocharacter and vertex. -/
theorem availableSimultaneousStandardBasis :
    AvailableSimultaneousStandardBasisStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx
  let D := (𝔅.datum F G hG).base
  exact ⟨availableSpecialCompactProperties_of_omegaCompatibleApartment hG 𝔅 h𝔅
      D.i D.isMaximalSplitTorus D.centralizer D.apartment D.isOmegaCompatible ν hν x hx,
    availableSpecialLeviInheritance_of_omegaCompatibleApartment hG 𝔅 h𝔅
      D.i D.isMaximalSplitTorus D.centralizer D.apartment D.isOmegaCompatible ν hν x hx,
    CongruenceGL.available_simultaneousStandardBasisAt 𝔅 hG h𝔅.isAvailableFor ν hν x hx⟩

end Langlands.BruhatTits.SpecialCompact
