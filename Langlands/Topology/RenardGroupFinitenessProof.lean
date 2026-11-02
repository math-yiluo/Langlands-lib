import Langlands.Topology.RenardGroupFinitenessStatements
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Lindelof

/-!
# Proofs of Renard II.3.2

The finite relative quotient is a compact discrete quotient of the actual
subgroup type. The ambient quotient is discrete by openness of the subgroup;
under sigma-compactness it is also Lindelöf, hence countable.
-/

set_option autoImplicit false

universe u

namespace Langlands.Topology.RenardGroupFinitenessProof

open RenardGroupFinitenessStatements

/-- Compactness of the ambient subgroup and openness of the relative subgroup
make the genuine relative coset quotient finite. -/
theorem relativeQuotientFinite : RelativeQuotientFinite.{u} := by
  intro G _ _ _ _ K K1 _ hKopen hK1compact _ _
  let : CompactSpace K1 := isCompact_iff_compactSpace.mp hK1compact
  exact Subgroup.quotient_finite_of_isOpen (K.subgroupOf K1)
    (Subgroup.subgroupOf_isOpen K1 K hKopen)

/-- Openness makes the ordinary subgroup quotient topology discrete. -/
theorem quotientDiscrete : QuotientDiscrete.{u} := by
  intro G _ _ _ _ K _ hKopen
  exact QuotientGroup.discreteTopology hKopen

/-- The ordinary quotient of a sigma-compact group is Lindelöf; its discreteness
then makes its carrier countable. -/
theorem quotientCountable : QuotientCountable.{u} := by
  intro G _ _ _ _ _ K _ hKopen
  let : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKopen
  let : LindelofSpace (G ⧸ K) := Quotient.lindelofSpace
  exact countable_of_Lindelof_of_discrete

/-- The unchanged aggregate, in every universe. -/
theorem assertions : Assertions.{u} :=
  ⟨relativeQuotientFinite, quotientDiscrete, quotientCountable⟩

end Langlands.Topology.RenardGroupFinitenessProof
