# Left adjoints for the factors of a category decomposition

This internal category theory helper derives a universal property from the
published `Langlands.Renard.IsCategoryDecomposition`. It uses only a category
with zero morphisms, with independent object, morphism and index universes.
It assumes no representation theory and no existence of a decomposition.

`Langlands.Renard.categoryDecompositionFactorInclusionRightAdjoint` is a
defined proof term for the same result as the theorem below, retaining all
category, index and decomposition parameters.

`Langlands.Renard.IsCategoryDecomposition.isRightAdjoint_ι` proves that the
inclusion of each factor has a left adjoint. For each ambient object `X`, the
proof chooses the coproduct cofan supplied by the decomposition. Its component
in the selected factor is the value of the left adjoint on objects. The
coproduct universal property constructs a projection onto that component:
it is the identity on the selected leg and zero on every other leg.

For an object `Y` of the selected factor, composition with this projection
gives a bijection from component-to-`Y` morphisms to `X`-to-`Y` morphisms.
The inverse composes with the selected coproduct leg. One inverse identity
uses the projection identity; the other uses coproduct extensionality and
vanishing of off-diagonal morphisms. The bijection is natural in `Y` by
associativity, so `Adjunction.adjunctionOfEquivLeft` supplies the left adjoint.
There is no size restriction on the index type and no finiteness condition.

The provenance is internal: this is a direct categorical consequence of the
two conditions in the published decomposition definition, using Mathlib's
coproduct and adjunction constructors. It supplies a step toward clause (a)
of `MaximalLeviBlockProjectionEquivalenceStatement` (module
`Langlands.Representation.Exponents.MaximalLeviBlockProjectionStatement`: the
inclusion of `M(M)_D` has a left adjoint) while retaining the decomposition as an
explicit hypothesis.
