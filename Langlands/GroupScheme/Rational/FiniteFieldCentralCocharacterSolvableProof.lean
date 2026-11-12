import Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableStatement
import Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableReduction
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Over a finite field, a group whose cocharacters are all central is solvable: proof -/

universe u

namespace Langlands.GroupScheme

/-- Over a finite field, a smooth connected affine group all of whose cocharacters are
central is solvable. -/
theorem finiteFieldCentralCocharacterSolvable :
    FiniteFieldCentralCocharacterSolvableStatement.{u} :=
  finiteFieldCentralCocharacterSolvable_of parabolicDynamic finiteFieldQuasiSplit

end Langlands.GroupScheme
