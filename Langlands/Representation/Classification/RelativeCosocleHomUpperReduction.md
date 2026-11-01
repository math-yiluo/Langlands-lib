# Reduction of the exact comparison to its upper inequality

Authors: Workers 526, 359, 435 and 845. The literal shape transport follows
Worker 435's assembly; Hom transport also uses the work of Worker 845.
The imported public lower-bound proof retains the injection of Workers
796, 526 and 359 and was assembled for publication by Worker 1127.
The namespace is `Langlands.RelativeCosocleHomUpperReduction`.

`UpperBoundCase` copies the entire nested telescope of
`GLRelativeCosocleHomComparisonStatement`, with all five independent
universes, actual refinements and flatten equality, the fine and middle
data, arbitrary irreducible analytic tempered coarse input, strict coarse
order and arbitrary irreducible actual outer quotient. Its conclusion is
only `finrank Hout ≤ finrank Hin` for the same actual Hom spaces. It adds
no support, chosen-equivalence or finite-dimensionality hypothesis.

`comparisonOfUpperBound` assumes that upper inequality. Fine
irreducibility and cuspidality transport across the actual shape equality.
Temperedness supplies coarse admissibility; irreducibility of the outer
quotient supplies a nontrivial carrier. The public
`fineRelativeHomLowerBound` then proves both finite-dimensionality
conclusions and `finrank Hin ≤ finrank Hout`. Antisymmetry gives the exact
comparison conclusion. This includes zero Hom spaces: no positive
multiplicity is assumed.

This is an internal deduction from the public lower-bound theorem. The
upper inequality is proved in `RelativeCosocleHomIsolationReduction`
from whole-induction isolation and finite generation, which the final
comparison entry module supplies.
