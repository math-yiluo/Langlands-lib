import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionOrbitRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotientAssembly

/-! # Quotients by smooth group actions with smooth stabilizers

A proof of `SmoothStabilizerActionQuotientStatement`: the first quotient
`exists_orbitRelationSpace` supplies the orbit relation space of the action, and
`actionQuotient_of_relationSpace` forms the quotient of `V` by it and compares it with
every fppf quotient of the action.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let a smooth group scheme `G` over `S` act on a scheme `V` locally of finite type over
`S`, with stabilizer scheme smooth over `V`. Then the fppf sheaf quotient of `V` by `G`
exists as an algebraic space, and for every such quotient the quotient map is smooth and
surjective and the quotient is locally of finite type over `S`. -/
theorem smoothStabilizerActionQuotient : SmoothStabilizerActionQuotientStatement.{u} := by
  intro S G V a hG hV hσ
  obtain ⟨B, s', t', q, hqs, hqt, hq, hinj, hsm⟩ :=
    SmoothStabilizerActionQuotient.exists_orbitRelationSpace a hG hV hσ
  exact SmoothStabilizerActionQuotient.actionQuotient_of_relationSpace hV hqs hqt hq hinj hsm

end Langlands.AlgebraicGeometry.AlgebraicSpace
