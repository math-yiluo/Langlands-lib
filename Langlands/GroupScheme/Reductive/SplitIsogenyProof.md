# General split reductive isogeny realization and fixed-torus extension

`Langlands.GroupScheme.splitIsogenyTheorem` proves the unchanged published
`SplitIsogenyTheoremStatement.{u}` for every universe `u`. Its two conjuncts
are realization of every supplied root-datum isogeny and the extension
criterion for a fixed actual torus isogeny. The statement module records
the original Milne Theorem 23.9 source and conventions; this module gives
a derived proof using the imported constructions.

The hypotheses are exactly those of the target: an arbitrary field `k`,
two connected reductive group schemes, specified split maximal tori,
finite reduced root data on their actual character and cocharacter
lattices, and the prescribed isogeny with exponent `ringExpChar k`.
There is no restriction on the root-dependent characteristic-power
factors, central torus directions, or smoothness of the kernels.

## Realization

`splitIsogenyExistence` first constructs the actual torus map with the
prescribed character pullback and cocharacter pushforward. The published
torus criterion makes it a finite, flat, surjective isogeny. The
`simpleIsogenyGraph` construction realizes the root-datum restrictions on
rank-at-most-one centralizers and forms their actual graph envelope over
that torus map.

The intrinsic chamber comparison supplies target simple-root coverage.
Together with source coverage, it certifies faithfully flat projection
geometry and connected reductivity of this same graph. The arbitrary-field
first-projection theorem now proves that its first projection to the
source group is an isomorphism. That theorem uses actual base change to
an algebraic closure and fpqc reflection, so the resulting isomorphism
is over the original field.

The graph torus followed by the first projection is the supplied source
torus inclusion. Maximality therefore transfers to the graph torus via
the closed first projection. The finite actual torus map and the closed
target torus inclusion give finiteness of the full scheme-theoretic
kernel of the second projection. Its recorded flat, surjective and
quasi-compact geometry then makes that projection an isogeny.

`exists_realization_of_graph_projections` inverts the first projection
and follows it by the second. This produces an actual group isogeny,
the commuting torus square, and both prescribed lattice identities.
The torus witness is the original constructed `torusMap hT' f`.

## Fixed torus and the complete theorem

The final theorem applies
`splitIsogenyTheorem_of_rootDatum_and_existence` to the published
`isogenyRootDatum` and the newly proved `splitIsogenyExistence`.
For necessity, the former theorem constructs the root-datum isogeny
from an actual extending group isogeny. For sufficiency, realization
produces a torus map with the prescribed character map, and character
extensionality for the split target torus identifies it with the fixed
input torus isogeny. Thus both assertions retain actual integral lattice
maps and full possibly nonsmooth kernels over every field.
