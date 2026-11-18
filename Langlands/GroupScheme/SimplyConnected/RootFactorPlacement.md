# Actual root-subgroup placement in simply connected product factors

Worker 509. This is derived geometric comparison material over arbitrary
fields with a supplied split maximal torus at every universe parameter. The input is an actual
`SimplyConnectedAlmostSimpleProduct` presentation of a semisimple group and
an actual split maximal torus. For the datum-indexed conclusions, an actual
root datum of that torus is also supplied.

`exists_root_subgroup_le_factor` places every nonzero actual root subgroup in
one actual product factor. Apply the published normal-root dichotomy to each
smooth connected normal factor, using `splitNormalRootDichotomy`. If a root subgroup lay in none of them, it
would centralize each of them on every test and refinement. Projecting a
commutation equation to each product coordinate then shows that it centralizes
the whole group, hence the acting split torus. The published noncentrality of
a nonzero root subgroup rules this out.

`root_subgroup_factor_unique` proves uniqueness. A point lying in two distinct
factors has trivial projection to each coordinate: each factor inclusion has
its own projection as retraction and has trivial projection to other
coordinates. Thus that point is the identity. If the whole root subgroup
lay in both factors, it would centralize the torus, again contradicting
noncentrality. No algebraic-closure hypothesis is used.

`rootFactorIndex` chooses the unique containing factor, with its exact
all-test subgroup containment and a characterization by that containment.
`rootDatumFactorIndex` applies it to each root of the supplied actual datum.

`pairing_eq_zero_of_root_le_and_not_le` proves that roots inside and outside
one normal factor are orthogonal in the specified ordered Cartan pairing.
The arbitrary-field split normal-root dichotomy makes roots outside the factor centralize it. Its
outside roots are closed under negation: otherwise the rank-one relation and
commutation of a root group with itself would force the nonzero opposite-root
pairing to vanish. An inside root group therefore commutes with both root
groups of each outside opposite pair. The rank-one commutation
criterion for all tests forces the ordered Cartan entry to be zero. This is the same
normal-root orthogonality argument already implemented in the published
absolute-almost-simple irreducibility proof, specialized to actual factors.

`pairing_eq_zero_of_rootDatumFactorIndex_ne` applies this to roots assigned
to different factors. Finally, induction on the equivalence relation generated
by nonzero off-diagonal simple Cartan entries proves
`rootDatumFactorIndex_eq_of_cartanConnected`: every connected component maps
to a single actual factor.

`pairing_eq_zero_of_commute_allTests` removes the infinitude hypothesis from
the previously published ordered-pairing criterion. Use the algebraic closure
as an actual test scheme over the original field; its units detect a nonzero
integral exponent. The published rank-one unit relation holds on this test,
so commutation with both opposite root groups forces the ordered pairing to
vanish. This does not extend the ambient group or its root datum.

This unit does not prove the reverse implication, identify an actual factor's
root datum with the whole component, descend the matching, or establish a
full-star factor comparison. All its placement and connectivity assertions
apply over arbitrary fields with the specified split maximal torus. It uses
no downstream local rank-one classification or Kneser–Tits input.
