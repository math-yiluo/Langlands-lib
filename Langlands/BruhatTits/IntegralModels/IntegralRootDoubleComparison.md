# Root multiples and doubled-root comparison for integral models

This is an internal supporting deduction from actual relative-root support,
canonical integral-torus specialization, and the intrinsic all-test root
functors. It does not assert a new original-literature result or prove the
facet-root survival criterion.

All fields and schemes are in an arbitrary universe `u`. The generic
vanishing lemmas assume a smooth affine group, a split torus map `i`, and a
nonzero character. If every positive natural multiple of that character is
absent from `relativeRoots i`, its intrinsic root functor is trivial.
The proof identifies the functor with the first cyclic filtration term,
then applies the published vanishing criterion for semigroups selecting no
ambient weights. The nonzero-character and splitness hypotheses ensure
that each positive multiple is nonzero, so absence from the root set
excludes the corresponding actual conjugation weight.

If `a` is an actual root, `HasRelativeRootSystem i` and the monomorphism
hypothesis on `i` exclude every multiple of degree at least three.
Consequently absence of `2 • a` makes the intrinsic `2 • a` root functor
trivial: its first multiple is excluded by the supplied absence and each
later multiple has degree at least four in `a`. Evaluating at the ground
field proves
`rootGroupPoints_double_eq_doubleRootGroupPoints`. Thus the intrinsic
doubled group agrees with the building convention that uses the identity
subgroup when the doubled character is absent.

For the integral comparison, `R` is a local domain with specified fraction
field `K`, `D` is supplied relative-component model data, `T` is its
compatible integral torus, `hT` makes the integral torus split, and `Q` is
the actual reductive quotient of the neutral special fibre. The generic
group is affine. The specialization is exactly `T.characterSpecialization
hT`, derived from the generic and residue base changes of this same torus.

`mem_relativeRoots_of_specialized_quotient_root` first includes every actual
quotient root in the actual neutral special-fibre support, then reflects
its membership through canonical specialization. Applying this to each
natural multiple proves `relativeRootMultipliers_quotient_subset`.
For an actual generic root `a`, the supplied generic
`HasRelativeRootSystem i` therefore excludes every quotient root
`n • T.characterSpecialization hT a` with `3 ≤ n`. This conclusion does not
require the first quotient root to survive.

When the first specialized root is absent, the proved bound discharges
the higher-multiple premise of `subgroup_eq_double_of_absent_roots`.
The quotient is smooth by its connected reductivity. Injectivity of the
canonical specialization supplies the nonzero character, and additivity
identifies the doubled specialization. The resulting
`quotient_subgroup_eq_double_of_absent_root` is an equality of intrinsic
subgroup functors on every test scheme, not just on rational points.

The entry construction `absentQuotientRootDoubleIso` applies uniqueness of
representatives to that equality. It compares any supplied representatives
and preserves the original homomorphisms into `Q.quotient`, as proved by
`absentQuotientRootDoubleIso_hom_comp`. The doubled character need not itself
be an actual quotient root. This unit supplies support and functor
comparisons only; the facet-depth criterion and derivative root datum
remain separate obligations.
