# Rational scaling of the normalized full Tate image

Author: Worker 1730.

This is an internal consequence of rationalization of actual abelian-scheme
homomorphisms and the normalized subgroup from `CommensurableLatticeTorsion`.
No external source is used.

Suppose actual maps `q : A → B` and `r : B → A` have both composites equal to
multiplication by `n²`, for a positive natural number `n`. The definition
`squareReverseIso` has rational forward map `(1/n) r` and inverse `(1/n) q`.
The tensor composition formula and the two composite identities prove that
these are inverse. The theorem `squareReverseIso_tate_apply` states its exact
effect on a full integral Tate element: apply `T(r)`, embed in the rational
Tate module, and multiply by `1/n`.

For an additive subgroup `L` of the full rational Tate module, assume that
every `n w`, with `w ∈ L`, has an integral representative, and that the full
integral image of `T(r)` is exactly the normalized subgroup, namely the
integral preimage of `n L`. Then `squareReverseIso_image_iff` proves that the
full integral Tate image under this rational isomorphism is exactly `L`.
The forward direction chooses the integral representative and lifts it
through `T(r)`. The reverse direction uses the normalized-image condition.
Both directions cancel `n` by rational scalar multiplication.

These results do not construct a geometric subgroup or quotient, nor do they
deduce the normalized integral-image premise. Those steps remain for the
lattice-realization proof.
