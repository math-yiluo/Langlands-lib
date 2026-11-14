import Langlands.GroupScheme.EvenOrthogonalForm.Reduction
import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.Proof

/-! # Forms of the split `SO_{2n}` are identity components of orthogonal groups

Proof of `EvenSpecialOrthogonalFormStatement` (Tits's realization of the forms of `SO_{2n}`,
`n ≥ 4`, as `O(q)⁰` for a quadratic form `q` over a central division algebra with orthogonal
involution), from the reduction `evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism`
and the automorphism theorem `specialOrthogonalAutomorphism`.
-/

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- **Tits's realization of the forms of `SO_{2n}`.** -/
theorem evenSpecialOrthogonalForm : EvenSpecialOrthogonalFormStatement.{u} :=
  EvenOrthogonalForm.evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism
    OrthogonalMatrix.specialOrthogonalAutomorphism

end Langlands.GroupScheme.Quaternionic
