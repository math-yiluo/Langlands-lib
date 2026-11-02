# Kernel pairs for actions on the tuple cross-cover pair scheme

This derived helper concerns the actual pair scheme of the symmetric tuple-tail
cross cover used in the Stacks Project, Lemma 68.8.6, Tag 07ST, and Lemma 68.8.3,
Tag 0BBN. The registered sources are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. The proof uses the existing scheme-valued
equivalence relation laws and comparison-arrow construction.

Work in arbitrary universe `u`, under the hypotheses on the original relation
in `TupleCrossCoverPair`. Write `H` and `L` for the higher and lower tails,
`c : P → H.U` and `v : P → L.U` for the cross-cover source and target,
and `B = P ×_{H.U} P` with projections `a,b`. Its lower relation arrow
`d : B → L.R` has target `v(a)` and source `v(b)`.

The helper takes an action `A₂` of `H` on `a ≫ c`, with two explicit compatibility
equations: acting on `B` preserves `a ≫ v` and `b ≫ v`. These are hypotheses of
the helper and are intended to be verified for the actual diagonal action.
No existence of such an action is asserted here.

`tupleTailCrossCoverPairAction_arrow` proves that `d` is invariant, since both
of its endpoints are invariant and the lower relation has a monic joint
endpoint map.

`tupleTailCrossCoverPairAction_isPullback` proves that the action relation is
the kernel pair of `d`. For two maps `x,y` into `B` with equal `d`, their second
cross coordinates have equal lower target. The existing cross-cover comparison
arrow gives a higher-tail arrow from the source of `y` to the source of `x`.
Act by this arrow on `y`. The resulting second coordinate equals that of `x`
by its lower target and higher source. Invariance of `d` and pair-scheme
extensionality then identify the full result with `x`. The monic joint endpoint
map of the action relation gives uniqueness.

`tupleTailCrossCoverPairActionAffineQuotientCover`, for `q < N+1`, applies the
existing compact-image construction to `d`, its kernel-pair square, its
étaleness, and its exact compact image. It produces finitely many invariant
affine opens of `B`, each with an affine quotient. It does not assert a
Noetherian first level or a descended action.
