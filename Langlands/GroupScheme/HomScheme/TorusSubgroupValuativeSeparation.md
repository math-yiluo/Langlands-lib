# Restriction of torus subgroups to schematically dominant bases

Author: Worker 668.

Restriction along a quasi-compact schematically dominant map of test schemes
is injective on the actual closed relative-torus subgroup functors. For the
containment argument, suppose the source of one group map is flat over the
base and the other group map is a closed immersion. The morphism from the
base-changed flat source to the original flat source is schematically
dominant. Containment after base change makes the defining ideal of the
closed subgroup vanish on this base-changed source. Schematic dominance
identifies the kernel of the composite with the kernel of the original
map. The closed-subgroup ideal criterion now gives containment on every
original test scheme.

A relative torus is smooth and hence flat. Applying the containment
argument in both directions reflects equality of evaluated torus subgroup
functors. The spectrum of the map from a discrete valuation ring to its
fraction field is quasi-compact and schematically dominant, so the small
admissible presheaf satisfies `UnramifiedFunctor.ValuativeSeparation`.

The embedding is internal to the actual subgroup and ideal-sheaf interfaces.
The specialization verifies the injectivity used for tori in SGA 3, Exposé XV,
Lemma 8.10(iv) and the application to the central torus functor just below it.
Both passages are on PDF page 62 of the Gille–Polo recomposition of
1 December 2008, corresponding to recomposed page 294 and original pages
471–472 (`sga3-expose-xv-raynaud-2008`). The Lean proof uses schematic
dominance and the full defining ideal.
