# Root restriction multipliers and uniform nonmultipliable depths

This internal helper specializes the published torus-then-field restriction
construction. It adds no claim directly attributed to the original literature.

`torusUniformRootDepthSubgroup` is defined for a homomorphism between tori
and a root datum valuation on the larger torus. It is the subgroup generated
by the filtrations at a single real depth `r` of all actual upper roots whose
restrictions are positive integral multiples of the lower character. This
construction uses the same positive restriction fibre as the published
multiplier-scaled subgroup, with every generator assigned depth `r`.

An actual upper root restricting to a positive multiple `m a_K` restricts to an
actual root for the smaller torus, by `rootRestriction`. The published base-change
root comparison reflects that root to `m a` over the original field. If the
original roots satisfy `HasRelativeRootSystem` and `2 a` is absent, the published
root-multiple bound forces `m = 1`.

Consequently `torusRestrictedRootDepthSubgroup` is, at any real depth `r`, the
`torusUniformRootDepthSubgroup` at uniform depth `r`. The proof compares the two indexed suprema and replaces each
positive multiplier by one. It does not assert the uniform-depth comparison
when the doubled lower root is present.
