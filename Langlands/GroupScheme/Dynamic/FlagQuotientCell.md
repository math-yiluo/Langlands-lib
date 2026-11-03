# Sections from a group cell in a scheme quotient

Author: Worker 424.

This internal construction joins `QuotientCell` to the published rational
translation adapter. It starts with actual group schemes `G`, `P`, `U`,
homomorphisms `iP : P → G`, `iU : U → G`, and an actual map `q : G.X → Q`
over any field at universe `u`. Its explicit hypotheses are monicity of `iP`,
smoothness, surjectivity and quasi-compactness of `q`, the exact right-coset
fiber criterion for `SubgroupFunctor.range iP` on every test scheme, and
open immersion of the actual multiplication `U × P → G`.

`flagQuotientCell` constructs an open of the same `Q` and a relative
morphism from that open to `G`. Smoothness makes `q` flat, so the existing
fpqc cell descent proves that `iU ≫ q` is an open immersion. Its actual open
image and the section obtained by inverting the isomorphism onto that image
give the construction. `flagQuotientCell_comp` verifies the section equation.

Because `iU` is a group homomorphism, it sends the identity rational point
of `U` to the identity of `G`. Naturality of the identity-test to ring-test
point equivalence therefore identifies its quotient image with the existing
identity coset. The full range-containment theorem of `QuotientCell`, applied
to that point, proves `range_identity_subset_flagQuotientCell`. This explicitly
handles the two existing conventions for rational points.

If every rational point of `Q` lifts to a rational point of `G`,
`localSections_of_open_multiplication` applies the published
`localSections_of_rational_lifts`. A smooth surjective quasi-compact `q` is an
effective epimorphism by the pinned Mathlib fpqc theorem, supplying the
descent premise of that adapter. The result gives the exact actual open,
relative section, full point-range containment and section equation near
every rational point, on this single model `Q`.

Provenance: the existing cell descent and section construction, the published
rational-translation construction, and elementary group-homomorphism and
category laws. This is a conditional consumer bridge. It does not construct
a quotient, prove its properness, identify a dynamic parabolic, establish an
opposite cell, or prove rational-point lifting. Those remain obligations for
the full `DynamicFlagQuotientExistenceStatement`. The bridge has no restriction
on field cardinality or characteristic and uses all relative test schemes in
its fiber criterion.
