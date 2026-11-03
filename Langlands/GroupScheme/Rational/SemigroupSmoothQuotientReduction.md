# Smooth quotient reduction for actual semigroup subgroup representatives

This internal construction assembles the geometric smooth quotient comparison
from three explicit proposition premises: semigroup realization, semigroup
functoriality, and the general smooth-surjectivity criterion for an actual
surjective identity differential. It does not prove those three premises.

`IsSmoothConnectedClosed.representative_properties` transfers closedness,
smoothness and connectedness from the chosen realization to every other
representative of the same all-test subgroup functor. It uses the canonical
isomorphism between representatives, smoothness under isomorphism over the
base, and the induced homeomorphism of schemes.

Given containment of the image semigroup functor, `semigroupPointsMapOfMapLe`
is actual postcomposition on its points over every test scheme.
`semigroupHomOfMapLe` lifts this natural family through the two
representatives. Its composite with the target inclusion is precisely the
source inclusion followed by the original group homomorphism.

If the two semigroup functors have their prescribed exact Lie images and the
ambient differential maps the selected source weight span onto the target
span, the induced homomorphism has surjective actual differential. To prove
this, map a target representative tangent vector to the ambient target
span, lift it to the source span, then lift through the source inclusion.
The target inclusion has injective differential, so the ambient
commutative diagram proves the required preimage equation.

The final reduction applies these constructions to a smooth equivariant
homomorphism between smooth affine group schemes over an arbitrary field
and universe. Semigroup realization gives smooth connected closed
representatives and their exact Lie images. Semigroup functoriality gives
the containment needed to construct the morphism. The proved theorem
`map_semigroupWeightSpan_eq_of_smooth` gives surjectivity on the selected
spans from actual scheme smoothness. The explicit general differential
criterion then gives actual scheme smoothness and surjectivity of the
induced morphism. This proves the exact
`SemigroupSmoothQuotientStatement` conditionally on the three premises.
The original morphism's scheme-surjectivity assumption is allowed by that
statement but is not needed by this argument.
