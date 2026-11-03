# Minimality of a proper rank-one dynamic parabolic

This derived construction works over every field `k` and universe `u`. The
ambient group scheme `G` is smooth, connected and affine. An actual split
commutative torus `T` maps to `G` by `i`; no maximality or injectivity is
assumed. Every actual nonzero relative Lie root of `i` is assumed to be
an integral multiple of one specified actual character `a`. The character
may be divisible. No root negation assertion is assumed.

`Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots` shows that a
cocharacter nonnegative on every actual root has full dynamic parabolic.
The split torus weight decomposition puts the entire actual Lie algebra
inside its nonnegative weight span, which is the intrinsic tangent image
of the parabolic. The canonical affine parabolic representative is smooth
by the published dynamic smoothness theorem. Every ambient dual-number
identity-kernel point consequently lifts to its Lie algebra. The published
full-Lie smooth-closed-subgroup equality theorem makes its all-test range
full. Connectedness is needed for the ambient group, not for the parabolic.

`RelativeRoot.isCentral_cross_difference_of_cyclic_relativeRoots` applies
the published root-annihilator centrality criterion to
`pair(a,ν) • eta - pair(a,eta) • ν`. Every root is an integral multiple
of `a`, so its pairing with this integral cocharacter is zero by bilinearity.
The conclusion is centrality on every scheme test, including nonreduced tests.

`rankOneParabolic_eq_of_pairings_pos` then proves equality of the actual
dynamic parabolics when both cocharacters pair positively with `a`.
Adding the central cross difference to `pair(a,eta) • ν` yields
`pair(a,ν) • eta`. Central-shift invariance identifies these parabolics,
and positive integral scaling invariance removes both factors.

`pairing_pos_of_rankOneParabolic_le` assumes the parabolic of `ν` is
proper and `pair(a,ν)>0`. If the parabolic of `eta` is contained in it,
then `pair(a,eta)>0`. Otherwise, any root negative on `ν` is a negative
multiple of `a`, hence nonnegative on `eta`. The published one-way
root-sign detection for parabolic inclusion would make this root
nonnegative on `ν`, a contradiction. Thus every root would be nonnegative
on `ν`, and the full-Lie result would contradict properness.

Combining these deductions, `rankOneParabolic_eq_of_le` gives equality
for every smaller dynamic parabolic on the same split torus. Finally,
`rankOneParabolicIsoOfLE` constructs the canonical isomorphism between
any two representatives of these subgroup functors, and its
`_hom_comp` theorem proves compatibility with the ambient inclusions.

This is an internal deduction from published dynamic tangent geometry,
root-annihilator centrality, central shifts, positive scaling and
uniqueness of subgroup representatives. It uses neither reductivity,
pseudo-reductivity, root negation, a root-system classification, nor a
root-sign inclusion structural statement. It does not prove properness
of the initial parabolic, conjugate arbitrary cocharacters to the same
torus, or prove intrinsic relative-root reflection existence.
