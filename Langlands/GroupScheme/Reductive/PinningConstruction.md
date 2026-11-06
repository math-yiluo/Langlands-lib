# Constructing pinnings from root lines and realized root data

Author: Worker 1472.

This is an internal construction from the published actual pinning,
root-datum realization and finite reduced integral-base interfaces.
It introduces no structural existence premise implicitly.

`RootPinning.ofRootLines` takes an actual torus inclusion `i`, a root
datum `P` satisfying `IsRootDatumOf i P`, a base `b`, and witnesses
`Nonempty (k ≃ₗ[k] weightSpace i χ)` for every `χ ∈ roots i`.
The root-range equation in `IsRootDatumOf` shows that every
`P.root a` for `a : b.support` is an actual root. Classical choice
then selects the required linear equivalence for each such index.
The result is a `RootPinning` on the same inclusion, datum and base.
This constructor does not require reductivity, maximality, finite
root indexing or reducedness separately, since it uses the supplied
line witnesses and root-range equation directly.

`SplitPinning.ofRootDatum` additionally takes actual connected
reductivity of `G`, splitness and maximality of the given torus
inclusion, a finite root index, and reducedness of the realized
datum. The published theorem
`Langlands.LinearAlgebra.RootDatumBase.nonempty_base`, through its
chosen `base`, provides a base on the original integral character
and cocharacter lattices. There is no additional assumption that
the roots span the full character lattice; central torus directions
are allowed. The constructor fills the pinning's remaining field
with `RootPinning.ofRootLines`. The resulting bundle uses exactly
the supplied torus, inclusion and realized root datum.

`SplitPinning.ofRootDatumExistence` takes a proof of the published
proposition `RootDatumExistenceStatement` as an explicit premise.
Applying it to the supplied group and split maximal torus produces
the finite reduced realized datum. The preceding constructor then
builds a witness of nonemptiness from that datum and the separately
supplied actual root-line witnesses. Classical choice extracts the
pinning bundle from that witness.

The field, schemes, root index and all coefficient-algebra tests in
the actual Lie weight spaces retain arbitrary universe `u`. These
constructors neither prove `RootDatumExistenceStatement` nor prove
that the actual root spaces are lines. They therefore give no
unconditional pinning existence result, pinned-isomorphism theorem,
automorphism section or quasi-split inner-form existence proof.
