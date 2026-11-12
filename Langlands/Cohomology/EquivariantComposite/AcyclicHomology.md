# Derived Hom from a single object on Hom-acyclic complexes

Author: Worker 141.

Let C be an abelian category whose objects lie in universe u and whose morphisms
lie in universe v, with a supplied derived-category model in the independent
universe w. The canonical map and its naturality apply to arbitrary
integer-indexed target complexes in C. The bijectivity theorem and bundled
acyclic-term equivalence additionally assume that C has enough injectives, that
the target complex K is bounded below, and that every term K^i is acyclic for
Hom_C(X, -): R^(q+1)Hom_C(X, K^i) = 0 for every integer i and natural number q.

This internal helper extends the published KInjectiveHomology construction of
Worker 134. It defines the canonical additive map from cohomology of termwise
Hom to shifted morphisms in any supplied derived category for arbitrary target
complexes. Its naturality proof follows the existing cycle-representative
argument and does not require K-injectivity. On K-injective targets the map is
the published additive equivalence.

For a bounded below complex whose terms are acyclic for Hom from the specified
object, the canonical map is bijective. Choose a quasi-isomorphism into a
bounded below complex of injective objects. The published acyclic-term theorem
makes its termwise Hom map a quasi-isomorphism, so it induces an isomorphism on
cohomology. Localization of the chosen map is an isomorphism as well. The
canonical map at the injective target is bijective by KInjectiveHomology, and
naturality therefore proves bijectivity at the original complex.

`acyclicHomologyDerivedAddEquiv` bundles that canonical map as an additive
equivalence. Its naturality is exactly the already proved naturality of the
map, so it does not depend on choices of compatible injective replacements.
The internal use of the standard derived category of abelian groups supplies
no extra hypothesis. The category's morphism universe and its supplied
derived-category universe remain independent.
