# Étale restriction and postcomposition of sheaves

For an étale scheme morphism \(f : Y \to X\), restriction precomposes a sheaf on the small étale site of \(X\) by the opposite of the étale site functor for composition with \(f\). A coefficient functor \(F : A \to B\) that preserves the sheaf condition on both sites acts by postcomposition. `restrictionSheafComposeIso` compares these operations in either order. Its components are identity maps on the underlying presheaves because functor composition is associative by definition.

The canonical identity and composition comparisons for restriction arise from the same site maps in both coefficient categories. The identity proof evaluates on an étale test and removes identity maps. For the composition law, after removing the identity components of the postcomposition comparison, the two maps agree by definition. This applies to the module universe lift of `Langlands.Sheaf.ModuleSheafUniverseLift`.
