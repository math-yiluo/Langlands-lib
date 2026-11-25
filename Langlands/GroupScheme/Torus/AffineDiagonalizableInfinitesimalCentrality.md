# Nilpotent centrality for diagonalizable sources and affine targets

This internal transport module derives its assertions from
`DiagonalizableInfinitesimalCentrality`, the affine-coordinate Hopf
presentation, and existing invariance of centrality under isomorphisms.
It introduces no additional literature assertion.

Let R be a commutative ring in any universe u, let H and G be group schemes
over Spec R, and assume that the total scheme of G is affine. If H is
relatively diagonalizable, then every homomorphism i from H to G is central
provided that its actual base change to Spec(R/I) is central for a
nilpotent ideal I of R. This uses the existing centrality predicate on all
test schemes and all restrictions of test schemes. There is no
smoothness, flatness, finite-presentation or immersion assumption on i.

`isCentral_of_hopfSpec_source` first assumes that the source is the Hopf
spectrum of the standard group algebra R[N], for any additive commutative
group N. Replace G by its coordinate Hopf spectrum using
`AffineCoordinates.hopfSpecIso`. Full faithfulness of the Hopf-spectrum
functor recovers the coordinate Hopf map. The reduced centrality hypothesis
transports through the base-changed target isomorphism. The existing
diagonalizable infinitesimal theorem lifts this centrality; postcomposing
with the coordinate isomorphism returns centrality of the original map.

`isCentral_of_diagonalizable_presentation` accepts any supplied isomorphism
from the standard diagonalizable group to H. Composing it with
`Diagonalizable.hopfSpecIso` reduces to the preceding theorem.
Precomposing with the inverse source isomorphism then returns the
original homomorphism. This presentation theorem does not require finite
generation of N.

`isCentral_of_isDiagonalizable` extracts the finitely generated character
group and group-scheme isomorphism in the Library's relative
`IsDiagonalizable` predicate. Its model is defined by pullback from Spec Z.
`Diagonalizable.baseChangeIso` identifies that model with the standard
diagonalizable group over R, giving the presentation needed above.

For a monomorphic i, `commGroupSchemeOfNilpotentQuotient` uses the lifted
centrality and the existing `IsCentral.commGroupScheme` construction.
The accompanying `toGrp` equality is reflexive: the entire source group
scheme and its operations are retained.

This module does not descend along a splitting fppf cover for a general
multiplicative-type source, lift multiplicative type from a special
fibre, or prove the fibrewise central-isogeny criterion.
