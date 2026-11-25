import Langlands.Cohomology.Profinite.TorsionDual

/-!
# Characters of subgroups extend

For an abelian group `A`, every character `X → ℚ/ℤ` of a subgroup extends to `A`
(`surjective_restrictCharacter`). The orthogonal complements for pairings with values in `ℚ/ℤ` are in
`Langlands.Cohomology.Profinite.TorsionDual`, the count along an exact sequence of seven terms in
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology

section Characters

variable {A : Type*} [AddCommGroup A]

/-- Every character of a subgroup extends: restriction `A^∨ → X^∨` is surjective. -/
theorem surjective_restrictCharacter (X : AddSubgroup A) :
    Function.Surjective fun χ : A →+ QZ => χ.comp X.subtype := fun ψ =>
  QZ.exists_comp_eq_of_injective X.subtype X.subtype_injective ψ

end Characters

end Langlands.GaloisCohomology
