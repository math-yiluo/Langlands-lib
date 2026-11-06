# Separation of finite coefficient spaces by ideal powers

This is an internal linear-algebra prerequisite for extracting coefficients from
finite infinitesimal neighborhoods of the identity. Its input is a supplied
finite-dimensional subspace `W` of a commutative algebra `A` over a field `k`.
The field and algebra have independent universes.

`quotientOn I N W` is the linear map obtained by restricting the actual quotient
algebra map `A → A / I^N` to `W`. The injectivity and functional-recovery results
below use this map.

`exists_comap_eq_bot` applies to any decreasing sequence of subspaces of `A`
whose intersection is zero. Pulling the subspaces back to `W` gives a descending
chain in a finite-dimensional vector space. The Artinian chain condition makes
the chain constant after some index. An element of that constant subspace lies
in every original subspace, by comparison with the maximum of the two indices;
separatedness then makes it zero.

For a Noetherian domain `A` and a proper ideal `I`,
`exists_quotient_injective` applies this argument to the scalar restrictions of
the powers of `I`. Mathlib's Krull intersection theorem supplies separatedness.
The resulting map from `W` to the actual ideal quotient `A / I^N` is injective.
No assumption that the quotient is finite-dimensional is needed.

`exists_quotient_functionals` chooses one such index before quantifying over all
linear functionals on `A`. A linear left inverse of the injective map into the
quotient lets each functional on `A` be reproduced, on all of `W`, by a linear
functional on `A / I^N`.

The provenance is this direct internal derivation from the Artinian chain
condition, Krull intersection and extension of linear maps over a field. No
external assertion is cited. These results alone do not identify a coordinate
algebra, prove tensor irreducibility or construct any Steinberg or big-cell data.
