# Morphisms of the actual torus norm subgroups

This internal construction restricts the actual rational-point map of an affine
commutative group-scheme morphism to the existing norm subgroups. Both groups use
the same finite Galois extension `L/k` and the same valuation of `L`. It constructs
`torusNormIwahoriMap` and proves that its underlying map is the original point map.
All fields and group schemes are at an arbitrary universe `u`; the valuation's
ordered value group has an independent universe.

## Provenance and scope

The source construction is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Definition 2.5.13, printed page 90 / PDF page 121. Its torus Iwahori subgroup is
the norm image of the character-valuation kernel over a finite Galois splitting
field. The present module uses exactly the Library construction
`torusNormIwahori`; its functoriality is a derived result, not a separately
numbered assertion attributed to the book.

The proof needs only affine commutative group schemes. It does not need a torus
or splitting hypothesis, invariance of the valuation under Galois automorphisms,
or a valuation on the base field. Accordingly those are not Lean hypotheses.
The common extension and valuation are explicit. This does not establish
independence of a splitting field, norm surjectivity, equality with a rational
character kernel, or naturality of arbitrary zero-subgroup data.

The source's 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, PDF pages 24–25, change the sign of the
character-valuation homomorphism and clarify the standing field assumptions
for Section 2.6. Those changes do not alter this norm-image construction or
its kernel functoriality. No project errata file for either source was found.

## Implemented proof

`rationalCoeffEquiv_map` identifies postcomposition before and after the
base-field coefficient comparison. `baseChangeCoeffEquiv_map` proves the analogous
identity for the actual pullback map, using its projection to the original
group scheme. These lemmas hold for arbitrary group schemes.

`rationalNorm_naturality` applies the two comparisons to the existing
coefficient-point theorem `GaloisPoint.norm_naturality`. It uses the actual
base-changed commutative morphism; no abstract point homomorphism is supplied.

For `map_torusNormIwahori_le`, represent a source point as the norm of a point in
the character-valuation kernel. The published
`map_characterValuationKernel_le` sends this point into the target kernel,
and norm naturality identifies its norm with the image of the original point.
Finally `torusNormIwahoriMap` restricts the original homomorphism to these
subgroups. The coercion theorem follows from that construction.
