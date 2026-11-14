# Noncommutation of adjacent simple root points

This internal helper concerns a supplied split pinning `p` of an affine group
scheme over a field `k`. Let `a` and `b` be distinct simple roots with
`p.rootDatum.pairing a b = -1`. Assume that there is a scalar `c₀` with
`c₀ ≠ 0` and `1 + c₀ ≠ 0`.

For any supplied root parametrizations `xa` and `xb` of the entire intrinsic
root subgroups for `a` and `b`, `adjacent_rationalPoint_not_commute` says
that `xa(s)` and `xb(t)` do not commute whenever both scalars are nonzero.
`adjacent_unitPoint_not_commute` specializes this to the coordinate-one points
of a supplied family of normalized simple-root parametrizations. The reverse
pairing is not needed. The field-size hypothesis remains explicit.

`AdjacentSimpleRootNoncommutationStatement` packages the coordinate-one result
as a proposition for the supplied pinning, and
`adjacentSimpleRootNoncommutation` proves it.

The implemented proof first uses the absence of mixed-sign combinations of
distinct simple roots to show that `U_a` commutes with `U_{-b}` on every
scheme test. Suppose that a nonidentity point of `U_a` commutes with a
nonidentity point `y` of `U_b`. The published opposite-factor-pair theorem
provides two points of `U_{-b}` whose product around `y` is a normalizer
point acting through reflection in `b`. The `U_a` point commutes with all
three factors and hence with that reflection point. Conjugation by the
reflection carries `U_b` to `U_{-b}`, so it then commutes with every
rational point of `U_b`.

Choose the published linked root parametrizations for `b` and `-b`.
Their rank-one relation at coordinates `1` and `c₀` expresses
`b∨(1 + c₀)` as a product of positive and negative root points and their
inverses. Thus the original `U_a` point commutes with this coroot value.
Torus equivariance, and the actual pairing `-1`, say that conjugation by
this value multiplies its nonzero root coordinate by `(1 + c₀)⁻¹`.
Injectivity of the root parametrization forces `1 + c₀ = 1`, contradicting
`c₀ ≠ 0`. The proof takes place on the rational scheme test and uses
the actual field-to-global-sections isomorphism.

Provenance is internal: the argument composes the published mixed-simple-root
exclusion, all-test root commutation, opposite-factor-pair reflection and
root-subgroup conjugation theorems with the published linked rank-one
relation. It adapts the coroot-scaling contradiction used in
`RootPairNoncommutation.exists_not_commute` to specified nonzero root
points. It does not assert an unrestricted characteristic or field-size
extension, root generation, or a normalizer-image equality.
