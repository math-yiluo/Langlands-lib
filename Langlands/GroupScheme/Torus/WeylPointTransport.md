# Transport of point Weyl quotients

This internal construction transports the quotient of actual normalizer points by actual centralizer points. It is derived from the Library's arbitrary-base normalizer and centralizer base-change results and the range invariance of a homomorphism under a source isomorphism. It makes no assertion that this point quotient represents a quotient scheme.

For every base morphism `b : S' ⟶ S`, the all-test normalizer of the pullback torus map is the pullback of its normalizer. The proof writes the normalizer as the normalizer of the pointwise range, then uses base change of ranges and of normalizers. Restricting the canonical pullback point equivalence gives `torusNormalizerBaseChangeEquiv`. The centralizer base-change theorem shows that this equivalence identifies the centralizer subgroups. `QuotientGroup.congr` therefore gives `pointWeylGroupBaseChangeEquiv` on every test scheme over `S'`. No flatness, representability, or geometric hypotheses are imposed.

Precomposing the torus map with an isomorphism of its group-scheme source preserves the pointwise range, hence both its all-test normalizer and its centralizer. These equalities give `pointWeylGroupSourceIsoEquiv`.

Over a field, for a torus map whose underlying scheme morphism is a monomorphism, `relativeWeylGroupPointEquiv` identifies the published rational quotient `N(k)/Z(k)` with the point Weyl quotient on the base test scheme. This uses the published equalities between the normalizer and centralizer functors at the base and their rational-point subgroups.

Combining this comparison with base change gives `fibreRelativeWeylGroupEquiv`: for an arbitrary field-valued base morphism whose pulled-back torus map is monomorphic, the rational quotient on that fibre is multiplicatively equivalent to the original point quotient evaluated on the same field-valued test scheme.
