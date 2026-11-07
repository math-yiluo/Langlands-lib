# The actual lowering string through a highest vector

This internal derived unit uses a field `k`, an affine group scheme `G` over
`k`, and a finite matrix representation `rho` of `G`. The construction
`rootStringMap rho xm v d` accepts any additive map `xm`, any vector `v`,
and any natural number `d`. It sends a coefficient vector indexed by `Fin d`
to the corresponding linear combination of actual divided-power images of
`v` in the original representation. The construction alone asserts no
injectivity or dimension.

All the theorems assume a supplied split pinning `p` with finite root index,
full integral coroot span `p.rootDatum.corootSpan Z = top`, and a supplied
certificate `p.IsHighestWeight rho lam`. For the cutoff theorem, take an actual
root `i`, an additive map equivariant by `-root i`, and a vector in the
highest-character space of weight `lam`. Require strict positivity of `root i`
on the polarization of the integral Weyl vector and require the pairing of
`lam` with `coroot i` to equal the supplied natural number `m`. Then all lowering
coefficients of degree greater than `m` vanish. This conclusion needs neither
an infinite field nor a nonzero vector.

The cutoff proof first uses signed torus equivariance to place each coefficient
in its shifted universal character space. An actual rational normalizer supplied
by the root datum carries this space to its reflection. A degree above `m`
would give a reflected weight strictly above `lam` on polarized rho, whose
space is zero by the highest-weight support bound. Invertibility of the
normalizer matrix then makes the original coefficient zero.

Independence and injectivity additionally require `Infinite k` and a nonzero
vector in the highest-character space. Supply two additive maps with opposite
characters `alpha` and `-alpha`, where `alpha` is strictly positive on the same
polarized Weyl vector, a cocharacter `nu` with pairing `(lam, nu) = m`, and the
linked root-cell relation for these maps and `nu` over every relative test
scheme. If `(m.choose a.val : k)` is nonzero for every retained index
`a : Fin d`, their original lowering images are linearly independent and
`rootStringMap` is injective. The proof applies each raising coefficient and
the normalized functional to a linear relation; the binomial pairings isolate
the corresponding scalar.

Under these same hypotheses, let `q` be prime, assume `CharP k q`, and let
`r` be natural. If `(lam, nu) = q^r - 1`, all binomial coefficients at the
retained indices `a : Fin (q^r)` are nonzero. Their `q^r` lowering images are
independent and their span inside the original representation has dimension
`q^r`. The infinite-field and nonzero highest-vector assumptions are retained.

The provenance is the previously proved actual character shifts, normalizer
weight transport, highest-weight support bound, rank-one binomial pairings and
Steinberg binomial identity. No external source or new existence result is
invoked. These are single-root conclusions; the full-unipotent top-action and
entire induced-space dimension obligations remain separate.
