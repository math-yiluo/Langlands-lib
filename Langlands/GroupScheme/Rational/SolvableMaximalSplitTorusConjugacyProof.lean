import Langlands.GroupScheme.Rational.CommSplitTorusConjugacy
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof

/-! # Rational conjugacy of maximal split tori in solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field, maximal split tori of a smooth connected affine solvable
group are conjugate by a rational point, with an isomorphism of their sources. -/
theorem solvableMaximalSplitTorusConjugacy :
    SolvableMaximalSplitTorusConjugacyStatement.{u} := by
  intro k _ G _ _ _ hG T T' i i' hi hi'
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨H, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hi.1.1.isTorus hi.1.2
  obtain ⟨H', j', hj', f', hf'⟩ :=
    exists_maximalTorus_extension_of_finiteType G i' hi'.1.1.isTorus hi'.1.2
  exact subgroupConjugate_of_conjugate_commutative_overgroups
    hi hi' j j' hj.2.1 hj'.2.1 f f' hf hf'
    (solvableMaximalTorusConjugacy k G hG H H' j j' hj hj')

end Langlands.GroupScheme
