# Open centralizers of subgroups of multiplicative type

This internal derivation proves that, in a relatively affine group over an
arbitrary base scheme, a represented centralizer of a closed subgroup of
multiplicative type is an open subgroup of its represented normalizer. The
subgroup is a commutative group scheme which becomes diagonalizable for a
finitely generated abelian character group on an fppf cover. Smoothness is not
assumed for the ambient group or for the subgroup.

`relativeMultiplicativeTypeCentralizerNormalizerInclusion` constructs the
inclusion from any supplied representatives of the centralizer and normalizer.
Its composite with the normalizer inclusion is the supplied centralizer
inclusion. It is an open immersion, and it represents the full preimage of
the centralizer subgroup functor on every test scheme.

The proof starts with the idempotent open locus of
`MultiplicativeTypeCentralizerOpen`. For a corepresented group whose embedded
diagonalizable subgroup has an all-test ideal cutout and projective quotient
coordinates, apply that locus construction to the universal point of the
represented normalizer. A representative of the centralizer preimage is
isomorphic to the open locus: one direction is factorization through an open
immersion, the other comes from the represented-subgroup property. The
monomorphism properties give the two inverse identities.

Over an affine base, the coordinate quotient of a closed diagonalizable
subgroup is identified with the global sections of the diagonalizable group.
These sections are isomorphic to its group algebra, which is free over the
base and hence projective. This discharges the projectivity hypothesis of the
locus construction. Ambient coordinate isomorphisms and the subgroup's
diagonalizable-model isomorphism transport the result to the supplied data.

An affine open cover extends the result to diagonalizable groups over
arbitrary bases. Finally the fppf splitting cover extends it to groups of
multiplicative type. The descent argument reuses Mathlib’s `FlatDescent` instance,
which derives fppf descent of open immersions from fpqc descent and Zariski
locality at the target by restricting
a surjective flat locally finitely presented morphism over an affine target
to a quasi-compact open with the same image. Applying this to the sum of the
pulled-back covering family detects the desired open immersion.

The proof reuses published character, affine cutout, represented-subgroup,
base-change and scheme-descent interfaces. It proves openness and the
canonical inclusion only; quotient existence and normalizer smoothness remain
separate assertions.
