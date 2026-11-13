import Langlands.GroupScheme.Quaternionic.LocalSpinRankOneReduction
import Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryProof
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof

/-!
# Quaternionic spin groups of rank one over local fields

Proof of `LocalSpinRankOneStatement`: over every nonarchimedean local field, a nondegenerate
quaternionic quadratic form of rank 4 or 5 and Witt index 1 (for an involution of the first
kind whose symmetric elements have dimension 3) has a spin group, and every spin group of it is
simply connected, almost simple and of split rank one.

The published reduction `localSpinRankOneReduction` derives this from two geometric
propositions, both of which are now proved in the Library:

* `ordinaryOrthogonalGeometry` : `OrdinaryOrthogonalGeometryStatement`
  (even orthogonal groups of rank `2m ≥ 6` are smooth with absolutely almost simple identity
  component, over every field);
* `quaternionicMoritaIsometry` : `QuaternionicMoritaIsometryStatement`
  (over an algebraic closure, the quaternionic isometry group becomes an ordinary orthogonal
  group of a nondegenerate form of rank `2m`; Tits 1968, §3, Prop. 6).
-/

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- **Local quaternionic spin groups of rank one.** Over every nonarchimedean local field, a
nondegenerate quaternionic quadratic form of rank 4 or 5 and Witt index 1 has a spin group, and
every spin group of it is simply connected, almost simple and of split rank one. -/
theorem localSpinRankOne : LocalSpinRankOneStatement.{u} :=
  localSpinRankOneReduction ordinaryOrthogonalGeometry quaternionicMoritaIsometry

end Langlands.GroupScheme.Quaternionic
