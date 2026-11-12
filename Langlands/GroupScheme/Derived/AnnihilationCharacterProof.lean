import Langlands.GroupScheme.Derived.AnnihilationStatement
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly

/-! # Proof: rational characters vanish on the derived subgroup after scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 6.19(d), character form. -/
theorem derivedCharacterAnnihilation : DerivedCharacterAnnihilationStatement.{u} := by
  intro k _ G D _ _ d hd R _ _ b χ
  have hdR : IsDerivedSubgroup ((GroupScheme.baseChange b).map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)
  exact hdR.characterRestrict_eq_zero χ

end Langlands.GroupScheme
