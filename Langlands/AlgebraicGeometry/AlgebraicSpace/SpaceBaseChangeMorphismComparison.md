# Iterated base change of morphisms

Internal categorical infrastructure for the stage-to-limit direction of
property descent. The natural isomorphism `baseChangeCompNatIso` packages the
published object comparisons `BaseChangeComparison.compIso`; its naturality is
the naturality of an algebraic-space morphism on the comparison of test schemes.

Every represented scheme-morphism property respecting isomorphisms is invariant
under this comparison, as is a property of the relative diagonal. The proof uses
Mathlib's invariance under an isomorphism in the arrow category. Local finite
type and smoothness, defined by chart squares, transport through an arrow
isomorphism by composing both chart maps with the relevant isomorphisms.

For a diagram of base schemes and any cone, a property of a base-changed map at
a stage can be carried to the cone point by base-changing along the corresponding
cone leg and using the natural comparison. The module implements this for all
represented scheme-relative properties that respect isomorphisms, and separately
for separatedness and smoothness. Thus it covers six of the eight properties in
`SpaceLimitPropertyDescentStatement`: closed and open immersion, affine, finite,
separated, and smooth. This direction requires no finite presentation,
cofilteredness or universal property for the cone.

These comparisons and preservation lemmas are derived from the imported Library
constructions, without an outside source. The descent direction, from a limit
property to a stage, and properness and connected fibres are not asserted here.
