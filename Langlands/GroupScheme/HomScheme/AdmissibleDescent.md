# Recovery and uniqueness of actual admissible descent

Author: Worker 1726.

This internal construction defines `matchingSubgroup` by applying all-test
subgroup descent to the local admissible families after the actual ambient
pullback comparison. Under `IsMatchingAdmissible`, its ordinary base change
equals each transported local subgroup. Its membership is Zariski local on
every relative test scheme, since the local admissible families have actual
monomorphic representatives.

`baseChange_eq_comap_restrict` compares ordinary subgroup base change with
actual family restriction by the direct/iterated ambient isomorphism. Applying
the inverse isomorphism cancels the comparison in `restrict_val_eq`.
`eq_of_restrict_cover` uses this identity and locality of monomorphically
represented subgroup equality to detect equality of actual admissible families
on an arbitrary open cover of the parameter scheme.

`restrict_matchingSubgroup` recovers the original local families from the
constructed subgroup, conditional on its admissibility. Its proof combines
local recovery for subgroup descent with cancellation of the ambient
comparison. Effective closed representability and the relative-torus property
are not supplied by this helper; they are needed to discharge that explicit
admissibility premise.

All constructions use actual scheme morphisms on all relative tests and are
derived internally from the previously established restriction, locality and
matching interfaces. No representing moduli scheme is assumed.
