# Open-subgroup fixed vectors of actual completed tensor slices

Author: Worker 2.

This internal construction identifies the fixed vectors of an entire closed
Hilbert tensor slice with those of its intrinsic smooth part. Under the existing
admissibility and nonzero-tail hypotheses, it identifies them with the fixed
vectors of the given original local factor. Generic dimension transports are
also provided.

## Inputs and actual spaces

`F : Type uF` is an arbitrary number field, `n` any natural rank, and coefficients
are complex. Original local factor carriers lie in independent universe `uV`,
without a chosen topology. The group at `v` is the actual general linear group
over the finite completion of `F`, with its existing matrix topology.

`P` is a supplied genuine finite tensor presentation of the actual invariant
automorphic form space `S`. The supplied invariant positive form `b` determines
the original global Hilbert completion. `sliceHilbertRange` is the existing
closed invariant slice in that completion, with its inherited action at the
actual local insertion. Its intrinsic smooth range is the intersection with
the ambient smooth subrepresentation for that local group.

## Fixed vectors and inherited norms

`TensorHilbertFixedAux.fixedInfSmoothEquiv` works over any commutative ring,
with independent ring, topological group and module universes. For any invariant
subspace and any open subgroup `K`, it identifies the `K`-fixed vectors of
the intersection with the ambient smooth part with the `K`-fixed vectors of
the original subspace. Both maps preserve the same underlying ambient vector.
For the inverse, `K` itself witnesses smoothness of a vector that it fixes.
Subtype extensionality proves fixedness, and both inverse laws are definitional.
The two ambient-value identities are proved by reflexivity.

`fixedInfSmoothIsometry` adds the inherited norm equality over a complex normed
space. The equality is definitional because both maps retain the original
ambient vector and both fixed spaces have the inherited subtype norms.

`sliceHilbertFixedIsometry` applies this construction to the actual completed
tensor slice. Its source is the open-subgroup fixed space of the intrinsic
smooth range, and its target is the fixed space of the entire closed range.
It requires neither admissibility, irreducibility, a nonzero tail nor compactness
of `K`. Zero tails and zero slices are included.

## Original-factor recovery and dimensions

`TensorHilbertFixedAux.factorFixedEquiv` first restricts a supplied genuine
equivalence onto the smooth intersection to the given open subgroup and then
composes `fixedInfSmoothEquiv`. The original factor carrier has a fourth
independent universe, separate from the ring, group and ambient carrier.
`factorHilbertFixedEquiv` applies this generic construction to the published
actual `factorHilbertSmoothEquiv`. It is a genuine complex-linear equivalence from the original
factor's fixed vectors onto the full closed slice's fixed vectors.
The explicit nonzero tail and original-factor admissibility are retained;
irreducibility is unnecessary.

`TensorHilbertFixedAux.factorFixed_finite` transports finite generation along
the generic fixed-space equivalence from an explicitly supplied finite-generation
proof. Over complex coefficients this is finite dimensionality.
`factorFixed_finrank` is the finite-rank equality of that same equivalence.
These helpers apply to any supplied equivalence onto the smooth intersection,
without a nonzero or dimension-one assumption. This module exports the actual
`factorHilbertFixedEquiv` constructor and these generic dimension laws; it does
not export specialized dimension-law wrappers for the completed tensor slice.

## Provenance and scope

The generic argument extends the existing `smoothPartFixedVectorsEquiv` route
to an invariant subspace intersected with the ambient smooth part. The actual
application reuses the published intrinsic smooth range, original-factor
equivalence and subgroup-fixed-space equivalence. Finite generation transport
and finite-rank equality use Mathlib. This is an internal derivation; no new
identification with original literature is asserted.

Presentations and positive forms remain supplied. The full closed slice is
not claimed to be a smooth representation. The unit does not construct input
data, assert occurrence or decomposition, identify a Haar-integrated operator,
or impose a canonical normalization or a fixed-space dimension.
