import Langlands.GroupScheme.Nilpotent.NoTorusUnipotent

/-! # A central maximal torus with unipotent quotient -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected affine geometrically nilpotent group over an arbitrary
field has a central maximal torus and an actual affine unipotent fppf quotient. -/
theorem nilpotentCentralTorusStatement : NilpotentCentralTorusStatement.{u} :=
  nilpotentCentralTorus.{u}

end Langlands.GroupScheme
