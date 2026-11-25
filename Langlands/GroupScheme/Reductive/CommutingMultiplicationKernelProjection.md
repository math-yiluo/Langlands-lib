# A closed coordinate projection of the commuting multiplication kernel

This internal helper concerns arbitrary group schemes `H`, `K`, and `G` over
an arbitrary scheme `S`, with maps `j : H → G` and `i : K → G` whose images
commute on every test scheme. It uses the published actual commuting
multiplication homomorphism `H × K → G` and its full scheme-theoretic kernel.
It introduces no structural existence assumption or literature assertion.

`commutingMultiplicationKernelRightProjection` is the composite of the kernel
inclusion with the second product projection. Together with the first
coordinate, it is the pullback of `j` along the scheme morphism sending
`k` to `i(k)⁻¹`. Inversion here is a morphism of schemes over `S`; it need
not be a group homomorphism. The proof rewrites the kernel equation as
`j(h) = i(k)⁻¹`. For each compatible pullback cone it pairs the two coordinates
and lifts the pair into the actual kernel. The two projection identities
and cancellation through the monomorphic kernel inclusion prove universality.
No monomorphism hypothesis on either factor is needed for this square.

Forgetting the base preserves the pullback square. Thus a closed immersion
`j` makes the second coordinate projection a closed immersion. If `i` is
monomorphic, the published right-coordinate centrality lemma shows that
this projection has image in the full centre of `K`, on every test scheme
and after every restriction. Consequently, if `K` has finite full centre,
the kernel is finite over `S`: it is a closed central subgroup of `K`, and
the published finite-centre factorization lemma applies.

These results retain nonreduced kernels. They require neither separatedness
of `G` nor finiteness of the centre of `H`. The intended use is multiplication
of a central torus and a semisimple subgroup; this helper alone does not assert
surjectivity or either central isogeny of `ReductiveDerivedCentralIsogenyStatement`.
