import Langlands.GroupScheme.Symplectic.StructureStatement
import Langlands.GroupScheme.SymplecticMatrix.AlmostSimple

/-! # The standard symplectic group is simply connected and absolutely almost simple -/

universe u

namespace Langlands.GroupScheme.Symplectic

/-- **Structure of `Sp_{2n}`.** Over every field, the standard symplectic group `Sp_{2n}` with
`n ≥ 2` is simply connected and absolutely almost simple, in every characteristic. -/
theorem structureStatement : StructureStatement.{u} :=
  fun K _ n hn => ⟨isSimplyConnected_groupScheme K n, isAbsolutelyAlmostSimple_groupScheme K n hn⟩

end Langlands.GroupScheme.Symplectic
