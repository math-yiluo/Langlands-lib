# Character-kernel factorization of intrinsic root subgroups

Over any field `k` in universe `u`, let `S` be a split torus, let `G` be any
group scheme and let `i : S → G` be a homomorphism. For a nonzero character
`a` of `S`, every homomorphism from `G` to a separated commutative group
scheme kills the full intrinsic root subgroup `RelativeRoot.subgroup i a`
on every scheme test. Neither affineness, finite type, smoothness,
connectedness, reductivity nor an actual-root hypothesis on `G` is required.

The proof chooses an integral cocharacter with positive pairing with `a`,
using the existing split-torus pairing theorem on the singleton `{a}` and
negating the cocharacter if necessary. The existing root-to-dynamic
inclusion embeds the root functor in its identity-limit subgroup.
A homomorphism to a commutative group is invariant under conjugation;
the existing identity-limit uniqueness theorem therefore makes it one
on that subgroup. Applying this to `Gm` shows that every rational character
is one on every test point of the intrinsic root functor.

For any actual representative `j : U → G` of this root functor,
`characterKernelFactor` constructs a group-scheme homomorphism
`U → kernel ψ` for each rational character `ψ` of `G`.
The all-test kernel-point equivalence first proves containment of the
representing range in the actual scheme-theoretic kernel. The existing
represented-subgroup factorization constructs the morphism, and
`characterKernelFactor_comp` proves that composing it with the actual
kernel inclusion is exactly `j`.

This is internal derived content from split-torus pairings, intrinsic
root contraction, identity-limit uniqueness and represented subgroup
factorization. It supplies character-kernel containment needed to
simplify integral root intersections in the parahoric-model construction.
It asserts no existence of integral tori, ambient models or valuation
filtrations and does not compare root points with building fixers.
