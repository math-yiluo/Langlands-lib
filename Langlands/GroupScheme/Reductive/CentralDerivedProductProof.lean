import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof

/-! # Central torus and derived subgroup generation for connected reductive groups -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive field group is generated scheme-theoretically by an actual
closed central torus and its actual derived subgroup: the subgroup multiplication map is an
epimorphism in `Over (Spec k)`. -/
theorem reductiveCentralDerivedProduct : ReductiveCentralDerivedProductStatement.{u} :=
  reductiveCentralDerivedProduct_of_torusSurjectivity.{u}
    reductiveCentralTorusSurjectivity.{u}

end Langlands.GroupScheme
