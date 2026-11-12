# Lifting a simply connected source through a central isogeny

Authors: Worker 124.

This internal construction extends the published common-refinement construction
from central isogenies to arbitrary homomorphisms out of a simply connected
semisimple group. The field and all schemes have arbitrary common universe.
The characteristic is unrestricted.

Let `f : C ⟶ G` be a homomorphism, with `C` simply connected in the Library's
semisimple sense. Let `q : H ⟶ G` be a central isogeny, with `H` connected
reductive and `G` separated over the field. The definition `liftHom` constructs
an actual homomorphism `a : C ⟶ H` with `a ≫ q = f`.
It is unique as a group-scheme homomorphism.

The construction adapts the published
`CentralIsogeny.CommonRefinementConstruction` and uses its actual descended
commutator morphism. Pair the commutator `C × C → C` with the canonical
lift to `H` of the commutator of the two images under `f`. This pointed
morphism into `C × H` generates a smooth geometrically connected affine
closed subgroup `D`, by `ImageGeneration.pointedImageGeneration`.
The two projections of `D` have equal composites with `f` and `q`:
they agree on the generating commutators and their ordered products, and
then agree on the whole smooth reduced generated group by dominance.

The first projection `D → C` is dominant because `C` is semisimple and
therefore perfect. The published
`isCentralIsogeny_fst_of_closedSubgroup` makes it a central isogeny.
The published central-isogeny semisimplicity transfer makes `D`
semisimple. Simple connectedness of `C` makes this first projection
invertible. Its inverse followed by the second projection is the required
lift. The chosen lift is packaged using existence of this actual
construction. Its factorization equation is `liftHom_comp`.

Uniqueness is the published cancellation theorem
`IsCentralIsogeny.cancel_of_connectedReductive`: a homomorphism from a
smooth connected reductive source cannot differ from another lift by a
nontrivial morphism into the finite cover kernel.

This construction does not assert any quaternionic spin model, determine
the spin-cover kernel or compute the preimage of a hyperbolic Levi subgroup.
It supplies the actual lifting operation required to compare a smaller
simply connected model with a supplied central cover.
