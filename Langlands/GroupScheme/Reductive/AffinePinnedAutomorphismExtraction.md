# Exact affine pinning from coordinate alignment and local pinning

This internal bridge assumes a single supplied `BasedCoordinateIso` from an
affine pinned model to itself, and concrete local pinning for the identity
pullback of its actual ambient automorphism. It proves the exact
`IsPinnedAutomorphism` predicate with label the inverse of the coordinate
root-datum equivalence.

The construction `pinnedAutomorphismOfBasedCoordinateIso` packages the actual
ambient automorphism together with its resulting exact pinning certificate.
Its underlying automorphism is precisely the one supplied by the coordinate
data; no alternative representative is chosen.

First, the all-test character formula in the supplied coordinate data is
promoted to an equality of actual fixed-exponent characters by pointwise
extensionality. Its inverse character equation aligns a source simple-root
weight with the target simple-root weight prescribed by the inverse label.
The published weight-line transport theorem then expresses the actual
differential of the chosen source generator as a unique unit times the chosen
target generator. The local-pinning coefficient rigidity theorem makes this
unit one over the original ring. Thus the chosen-vector equations have the
same fixed label as the full character formula.

The base-support condition and character clause follow directly from the
inverse of the supplied based coordinate equivalence. No connectedness or
field assumption is needed here: the single global coordinate alignment and
local pinning are explicit inputs. Their existence, and the parent
automorphism-group decomposition, remain separate obligations.

On a nonempty original base, the module also proves that an exact pinned
automorphism has at most one label. Closedness makes the torus inclusion
monomorphic, so two labels for the same automorphism have the same actual
torus map. Cancelling that torus isomorphism in the actual character equations
identifies the two fixed-exponent characters. At one residue-field point,
the published character-coordinate equivalence makes the exponent vectors
equal. A root-datum equivalence is determined by its full weight map, so the
labels coincide. In particular the identity actual automorphism has only the
identity label. The separate fixed-exponent injectivity lemma only needs one
specified field-valued point of its arbitrary base.
