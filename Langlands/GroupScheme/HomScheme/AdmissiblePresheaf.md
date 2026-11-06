# The small presheaf of actual closed torus subgroups

Author: Worker 1726.

For an actual group scheme over `Scheme.{u}`, `AdmissibleSubgroup` consists
of its all-test subgroup functors satisfying the published `IsAdmissible`
condition. `AdmissibleRepresentative` packages an actual closed torus
inclusion representing one such functor, and `admissibleRepresentative`
chooses one using the existence assertion in `IsAdmissible`.

The full ideal sheaf kernel of the chosen inclusion determines the functor.
Indeed, the Library theorem `IsClosedSubgroup.mem_range_iff_ker_le` detects
factorization on every relative test scheme by containment of full kernel
ideals. Equality of chosen ideals therefore gives equality of the subgroup
functors. Since these ideal sheaves live in `Type u`, this injection proves
`Small.{u}` of admissible subgroups without restricting the test schemes.

`evaluate_eq_of_range_eq` proves that actual family evaluation depends only
on the original all-test subgroup. Base change preserves range, and the
canonical ambient comparison transports the two equal ranges in the same
way. Identity evaluation agrees with the original range: the actual
evaluated inclusion is the original inclusion precomposed with the
canonical source identity-pullback isomorphism. `restrict` evaluates a
chosen representative. The preceding invariance makes the choice
irrelevant; the Library `evaluate_comp` proves composition of restrictions.

`admissiblePresheaf` is this presheaf on the over category, retaining the
original larger type. `smallAdmissiblePresheaf` conjugates each actual
restriction by `equivShrink` to give values in `Type u`.
`smallAdmissibleEquiv` decodes its sections as the actual admissible subgroup
functors and commutes with restriction. `totalAdmissiblePresheaf` applies
the Library `overTotal` construction: a section over a scheme includes its
actual map to the fixed base and the corresponding admissible subgroup.

This is an internal construction from the Library actual-family interface,
full defining-ideal membership criterion, standard pullback comparisons,
and Mathlib universe shrinking. It asserts neither sheafness nor
representability of the presheaf; effective subgroup gluing remains a
separate step.
