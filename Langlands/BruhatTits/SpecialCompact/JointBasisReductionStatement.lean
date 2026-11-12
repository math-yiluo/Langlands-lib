import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.BruhatTits.SpecialCompact.AvailableBasisStatement
import Langlands.BruhatTits.Iwasawa.AvailableStatement
import Langlands.Representation.Plancherel.AvailableRenardCartanStatement
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingStatement
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexStatement
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement

/-!
# Reduction of the joint special-compact existence target to conditional statements

The joint existence target `JointSpecialCompactBasisExistenceStatement` follows from the
existence of a valid corrected KP assignment together with six conditional statement targets
on valid or available data. This module states the reduction; it proves nothing.
-/

noncomputable section

universe u

namespace Langlands.BruhatTits.SpecialCompact

open Langlands.Geometry.Building

/-- If some corrected KP assignment is valid, and the torus rebasing, special vertex
existence, simultaneous basis, Iwasawa, Renard Cartan and Levi compact statements hold,
then the joint special-compact, Iwasawa, Cartan and simultaneous-basis existence target
holds. -/
def JointBasisReductionStatement : Prop :=
  (∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid) →
    ValidAssignmentTorusRebasingStatement.{u} →
    AvailableSpecialVertexExistenceStatement.{u} →
    AvailableSimultaneousStandardBasisStatement.{u} →
    Iwasawa.AvailableIwasawaStatement.{u} →
    Plancherel.RenardCartan.AvailableRenardCartanStatement.{u} →
    AvailableSpecialLeviCompactStatement.{u} →
    JointSpecialCompactBasisExistenceStatement.{u}

end Langlands.BruhatTits.SpecialCompact
