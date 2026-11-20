import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralDescentReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityProof

/-! # Descent of central homomorphisms from groups of multiplicative type (SGA 3, IX, 5.4) -/

universe u

namespace Langlands.GroupScheme

/-- SGA 3, Exposé IX, Corollaire 5.4: central homomorphisms from groups of multiplicative type
descend uniquely along faithfully flat quasi-compact base changes, or base changes with a
section, whose geometric fibres are connected. -/
theorem multiplicativeTypeCentralDescent : MultiplicativeTypeCentralDescentStatement.{u} :=
  MultiplicativeTypeCentralDescent.descent_of_rigidity multiplicativeTypeCentralRigidity

end Langlands.GroupScheme
