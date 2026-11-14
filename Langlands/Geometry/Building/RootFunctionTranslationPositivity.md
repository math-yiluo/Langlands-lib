# Strict positivity from nonnegative nearby torus translations

Author: Worker 200.

The module defines
`RootFunctionFamily.NonnegativeNearTranslations φ a g`: for every real
cocharacter vector `v`, the value of `g` in character direction `a` is
nonnegative at `t • v +ᵥ φ` for all real `t` in some neighbourhood of zero.
The neighbourhood may depend on `v`. Only the usual topology on the real
parameter is used; no topology is imposed on the space of root-function
families.

For a split torus and a nonzero character, the theorem
`RootFunctionFamily.strictPositive_iff_nonnegativeNearTranslations` proves
that this condition is equivalent to `0 < φ a g`. The family is arbitrary:
the proof assumes no root-valuation axiom, group reductivity, root membership,
or nonidentity condition on `g`. It includes the infinite-value case.
`RootFunctionFamily.not_nonnegativeNearTranslations_of_eq_zero` gives the
value-zero consequence.

## Implemented proof and provenance

This is an internal consequence of the published torus translation formula
`RootFunctionFamily.vadd_apply`, the published nondegeneracy result
`exists_eval_ne_zero` for split tori, and elementary real topology.

If the initial value is infinite, all its translates are infinite. If it is
a positive real number `q`, continuity of
`t ↦ q + t * eval S a v` gives a neighbourhood on which it remains positive.
Conversely, the neighbourhood condition at zero implies `q ≥ 0`.
If `q = 0`, choose a vector with nonzero character evaluation and rescale it
to obtain evaluation `-1`. Every neighbourhood of zero contains a positive
real parameter, where the translated value is negative. This contradiction
proves `q > 0`.

## Role and limits

The intended application is the neighbourhood argument in the fixed-point
depth-zero proof. The published torus-then-field restriction law carries
descended translations to the translations appearing in this criterion.
Thus an eventual nonnegativity statement along those paths suffices for
strict positivity, without requiring the restricted family to satisfy V5.

This module does not construct integral models or identify their radical
preimages. A separate geometric argument must prove that elements of such a
preimage satisfy the neighbourhood condition before this criterion can be
used to exclude value-zero elements.
