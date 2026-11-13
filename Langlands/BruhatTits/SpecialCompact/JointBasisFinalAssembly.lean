import Langlands.BruhatTits.SpecialCompact.JointBasisReductionProof
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingProof
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactProof
import Langlands.BruhatTits.Iwasawa.AvailableProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.BruhatTits.SpecialCompact.JointBasisCartanAssembly

/-! # The remaining inputs to the joint special-compact existence proof -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- Apply the four published structural dischargers to the published common-witness
reduction. The three explicit inputs are still open and this is not an unconditional
proof of the joint existence statement. -/
theorem jointSpecialCompactBasisExistence_of_remainingInputs
    (hAvailability : Langlands.Geometry.Building.BruhatTitsAvailabilityStatement.{u})
    (hBasis : AvailableSimultaneousStandardBasisStatement.{u})
    (hCartan : Langlands.Plancherel.RenardCartan.AvailableRenardCartanStatement.{u}) :
    JointSpecialCompactBasisExistenceStatement.{u} :=
  jointBasisReduction hAvailability validAssignmentTorusRebasing
    availableSpecialVertexExistence hBasis Iwasawa.availableIwasawa hCartan
    availableSpecialLeviCompact

/-- The joint target follows from a valid corrected KP assignment and the
simultaneous basis statement. The same-compact Levi Cartan clause is proved
internally from published results under that global validity. -/
theorem jointSpecialCompactBasisExistence_of_availability_and_basis
    (hAvailability : Langlands.Geometry.Building.BruhatTitsAvailabilityStatement.{u})
    (hBasis : AvailableSimultaneousStandardBasisStatement.{u}) :
    JointSpecialCompactBasisExistenceStatement.{u} := by
  obtain ⟨𝔅₀, h𝔅₀⟩ := hAvailability
  intro F _ _ _ _ G hG S i hi ν
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝔅, h𝔅, hS, hVi⟩ := validAssignmentTorusRebasing 𝔅₀ h𝔅₀ F G hG S i hi
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  refine joint_of_valuationBuildingData (𝔅.datum F G hG).base.toValuationBuildingData
    (availableSpecialVertexExistence F G hG 𝔅 hA) (hBasis F G hG 𝔅 h𝔅)
    (fun ν hν x hx => ((Iwasawa.availableIwasawa F G hG 𝔅 hA ν hν).1 x hx).2.2.1)
    (Langlands.Plancherel.RenardCartan.validSpecialCompactRenardCartanComparison
      F G hG 𝔅 h𝔅) ?_ hi hS hVi ν
  intro ν hν x hx J hJ
  have : IsAffineHom (Standard.leviScheme (𝔅.datum F G hG).base.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom _ ν J).isAffineHom
  obtain ⟨hM, 𝔅M, hAM, hSM, hiM, xM, hxM, hK⟩ :=
    availableSpecialLeviCompact F G hG 𝔅 h𝔅 ν hν x hx J hJ
  rw [← hK]
  exact parabolicPointProductFamily_of_heq hSM hiM _
    (fun ν' hν' => ((Iwasawa.availableIwasawa F _ hM 𝔅M hAM ν' hν').1 xM hxM).2.2.1) ν
    (isGenericCocharacter_leviTorusHom hν J)

end Langlands.BruhatTits.SpecialCompact
