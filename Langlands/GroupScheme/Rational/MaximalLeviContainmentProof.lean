import Langlands.GroupScheme.Rational.MaximalLeviContainmentStatement
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Levi subgroups of proper parabolics containing a maximal Levi: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Maximal-Levi containment.** Let `P = MN` be an actual maximal proper rational
parabolic of a connected reductive group `G` over a field, with rational Levi `M`. If the
rational Levi `L` of an actual proper rational parabolic `Q` of `G` contains `M` as a
subgroup functor of `G`, then `L = M`. The published reduction from Milne's Theorem 25.1
is applied to its published proof. -/
theorem maximalLeviContainment : MaximalLeviContainmentStatement.{u} :=
  maximalLeviContainment_of_parabolicDynamic parabolicDynamic

end Langlands.GroupScheme
