# Monomorphisms and trivial scheme-theoretic kernels

Worker 878.

For homomorphisms of actual group schemes over an arbitrary scheme, this internal
kernel API proves that the homomorphism is monomorphic exactly when the structure
map of its full scheme-theoretic kernel is an isomorphism. No finiteness,
commutativity, flatness, or separatedness assumption is used.

The forward implication uses the kernel pullback square. Its structure map is a
monomorphism and has the kernel's unit section, so it is an isomorphism. For the
reverse implication, an isomorphic kernel structure map makes all groups of
kernel points trivial. The published `kernelPointsEquiv` then identifies each
pointwise kernel with the trivial subgroup, so postcomposition is injective on
every test scheme. The definition `kernelBaseIsoOfMono` packages the resulting canonical isomorphism
from the kernel scheme to the base; its forward map is exactly the kernel
structure map. The final lemma transports the criterion through the
published `kernelBaseChangeIso`.

This is a derived categorical ingredient for the kernel proof of SGA 3 IX,
Corollaries 6.6 and 6.7. It claims only the kernel criterion and its base-change
compatibility, and does not claim those spreading corollaries.
