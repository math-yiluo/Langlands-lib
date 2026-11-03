# Closed equivariant embeddings of homogeneous reduced schemes

Internal supporting construction for the centralizer–Borel intersection argument,
by Worker 1438. It uses the published generic-flatness and translation argument
of Worker 716 in `OrbitMapFlatProof`, and the actual scheme-action interfaces.
It defines the reduced closed image `reducedClosedImage` and its canonical
inclusion `reducedClosedImageι`. This helper supplies no proof of the main centralizer statement.

Over an algebraically closed field, a rational point in the topological image
of a morphism between schemes locally of finite type has a rational lift. The
proof finds a closed point in the nonempty closed inverse image of the rational
point and uses the identification of closed points with rational sections.

The main helper takes a reduced scheme `X` of finite type, a scheme `Y` locally
of finite type, actions of the same group scheme on both, and an equivariant
monomorphism `f : X → Y`. It assumes a rational point of `X` whose orbit contains
all rational points of `X`, and closedness of the topological image of `f`.
It proves that `f` is a closed immersion.

The proof factors `f` through the reduced closed subscheme `O` on its image.
Ambient rational translations restrict to automorphisms of `O`; equivariance
makes their squares with the translations of `X` commute. Generic flatness
provides a nonempty open of `O` over which the factor is locally flat.
Rational lifting and transitivity show that the translates of this open cover
`O`, using closed points in a hypothetical nonempty closed complement. The
commuting automorphisms transport local flatness to every source point.
The factor is therefore a flat, quasi-compact, surjective monomorphism,
hence an isomorphism by faithfully flat descent.
Composition with the closed inclusion of `O` proves the result.
