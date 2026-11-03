# Actual root subgroup and character-kernel transport between acting tori

This internal construction transports the existing all-test character-kernel and
root subgroup constructions between different acting commutative group schemes.
It works over an arbitrary base scheme B. The acting groups need not be tori.
No smoothness, reductivity, splitness, monomorphism or root-membership premise is
needed. The supplied isomorphisms and their commuting square remain explicit.

For an isomorphism e from S to S', the existing character-lattice identification
sends a to a' = e inverse followed by a. `characterKernelCongr e a` is an actual
group-scheme isomorphism from the full kernel of a to the full kernel of a'.
Its forward map followed by the target kernel inclusion equals the source
inclusion followed by e. Its inverse satisfies the corresponding inverse
formula. Both statements concern scheme-theoretic kernels, including nonsmooth
kernels, on all test schemes.

Suppose i maps S into G, j maps S' into H, f is an isomorphism from G to H,
and i followed by f equals e followed by j. The extension equation defining
`RelativeRoot.subgroup i a` transports under f and under reparametrization by
e inverse. The identity value at zero is preserved. Applying the same argument
to both inverse isomorphisms gives the literal subgroup-functor equality

`(RelativeRoot.subgroup j a').comap f.hom = RelativeRoot.subgroup i a`.

`subgroupTransportEquiv` restricts f to a multiplicative equivalence on these
subgroups over every scheme test. Its inverse restricts f inverse. The two
ambient formulas record these exact maps.

For an actual base point g with i followed by Int(g) equal to e followed by j,
`transporterConjEquiv` specializes this equivalence to the same actual g. Its
forward map is x mapped to g_U times x times g_U inverse; its inverse is x
mapped to g_U inverse times x times g_U. No alternative transporter or
normalizer lift is chosen.

The kernel isomorphism is induced by the isomorphism of the defining pullback
diagrams. The root subgroup proof extends the published same-torus
reparametrization argument to a homomorphism from a different acting group,
then reuses the existing ambient-map orbit and extension laws. This is an
internal derivation, with no new external structure assertion. Worker 118
identified the cross-torus interface needed for apartment charts.

These constructions supply neither torus conjugacy nor existence, a geometric
root realization, a comparison of Lie weight spaces, building axioms, topology,
affine apartment maps or root valuations. The quotient and lattice comparisons
used elsewhere retain their own hypotheses.
