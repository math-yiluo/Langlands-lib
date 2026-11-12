# Assembly of the actual finite cuspidal embedding target

This derived construction assembles the actual intermediate steps of Renard
VI.7.2, printed pp.181–184 / PDF pp.187–190 in the registered 2026 edition.
It retains four representation-theoretic inputs: uniqueness of the original
Bernstein inertial support, the actual whole cuspidal inertia product
decomposition on rational Levi groups, the actual finite cuspidal induced
embedding, and arbitrary-inertia Jacquet exclusion. These inputs are not
proved here, and the full unconditional target remains open.

`bernsteinFiniteInducedCofan` applies the actual induced Levi inertia cofan
construction at each standard-Levi index of the finite embedding target.
It composes these supplied cofans with the actual direct-sum cofan using
the sigma-cofan universal property. The resulting vertex is the original
finite induced target, with actual summands, legs, Bernstein inertial class
labels and the original saturated block property. It requires no global
existence of coproducts at the larger inertia-index universe.

`isBernsteinCoproductOfComponents_of_labelledPresentation` regroups those
actual labelled leg images by their original Bernstein inertial classes.
The original support-uniqueness input proves disjointness. This is the
published class-indexed component-coproduct predicate at the same vertex.

`bernsteinCoproductOfComponents_of_finiteEmbedding` obtains the actual
injective intertwiner into the finite target, constructs that target's
component coproduct, splits its actual invariant image and pulls it back
to the source's original carrier universe using the actual source-to-image
equivalence. The source and field universes remain independent.

`bernsteinCategoryDecomposition_of_representationInputs` specializes the
global rational finite-embedding statement to this actual standard family.
The relative root, standard cocharacter, Levi intersection and Hausdorff
point-topology inputs are discharged by the published geometric results.
It pairs the constructed objectwise decomposition with the published
support-uniqueness consequence that every off-diagonal block morphism
vanishes. Its conclusion is the exact original category-decomposition
predicate for this family, conditional on the four explicit inputs.
