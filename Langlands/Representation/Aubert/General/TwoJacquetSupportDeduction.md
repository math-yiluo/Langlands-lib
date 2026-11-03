# Two Jacquet detectors from associated support

This internal deduction connects the published associated-support detector to
the actual two-factor construction. It works with two possibly different
standard Levi subgroups. It does not require a normalizer lift to preserve one
Levi, a finite-length premise on the induction, or vanishing of the induction's
Jacquet modules away from those two indices.

The inputs are actual standard subgroup families, their semidirect
decompositions and closed radicals, the inside-Levi decompositions and Levi
closedness used by `IsLeviCuspidal`, and an association relation.
`SupportCategoryIrreducibleJacquetDetectionTarget` remains an explicit
representation-theoretic premise. A second explicit premise says that every
associate of the inducing index `I` has index `I` or `J`; no equality of these
indices or their Levi groups is assumed.

`two_jacquet_nontrivial_of_support_detection` first puts an irreducible actual
subquotient in the same support category using its published subquotient
closure. The supplied detector gives a nonzero Jacquet module at some associated
index. The two-index premise identifies it with one of the two displayed
indices. This step needs no Jacquet exactness or vanishing premise.

`two_jacquet_nontrivial_cuspidalInduction_subquotient` specializes this result to
actual normalized induction. Identity association and the irreducible inducing
object's exact inside-Levi cuspidality put this induction in the support category
by `isInSupportCategory_cuspidalInduction`.

`inductionTwoJacquetFactorsOfSupportDetection` assumes additionally that both
Jacquet modules of the induction are irreducible, that the radicals are limits
of compact subgroups, and that the induction is reducible. It supplies the
preceding detector to `inductionTwoJacquetFactors`. The resulting data are one
actual nonzero proper invariant subspace `S`, its actual quotient `Q`, their
irreducibility, and the full pattern

- `r_I(S)` is equivalent to the inducing representation;
- `r_I(Q)` has a subsingleton carrier;
- `r_J(S)` has a subsingleton carrier;
- `r_J` of the induction is equivalent to `r_J(Q)`.

These are actual equivariant linear equivalences and actual vanishing
statements. The constructor uses the existing length bound and actual quotient;
it adds no finite-length or splitting assumption.

`InductionTwoJacquetFactors.other_jacquet_subsingleton` separately propagates
vanishing at any further index `K` to both literal factors. The canonical
inclusion and quotient map make them actual subquotients of the induction.
`jacquet_subsingleton_of_isSubquotient`, using compact-limit exactness for
`U K`, then gives both conclusions. This lemma imposes no inequality between
`K` and the distinguished indices.

The field is complex, the group and representation universes are independent,
and the inducing carrier has universe `max uG uV`, as required by the support
category's quantifiers. The index type is arbitrary; no global `Fintype` is
needed for these deductions.

The provenance is the displayed elementary specialization of the published
support-category closure and detector interface, `TwoJacquetFactors`, and
`SupportCategoryReductions`. This module proves neither the supplied general
support detector nor the two-index root-association theorem, simplicity of the
rational middle Jacquet modules, exponent signs or the analytic criterion. It
does not prove `RationalRankOneSelfAssociationStatement`.
