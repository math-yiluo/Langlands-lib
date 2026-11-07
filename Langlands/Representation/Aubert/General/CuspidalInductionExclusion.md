# Proper-induction exclusion from a supplied actual cuspidal splitting

This internal conditional component uses actual smooth representations, actual
normalized induction and Jacquet restriction, actual subquotients, and an actual
binary coproduct. It does not prove existence of a cuspidal splitting.

`HasCuspidalRemainderSplitting` asks that an ambient object be the vertex of an
actual coproduct cofan on two smooth representations. The `true` component is
cuspidal for the supplied family of semidirect decompositions. Every nonzero
actual subquotient of the `false` component fails that same cuspidality
predicate. The condition is local to one ambient object and weaker than the
whole-category all/no-subquotient decomposition: it tests the cuspidal component
itself, without testing all its subquotients.

`no_cuspidal_subquotient_of_splitting` assumes this condition and that every map
from a cuspidal object to the ambient object is zero. The true coproduct leg is
therefore zero. The coproduct universal property constructs an inverse to the
false leg, giving an actual isomorphism from the ambient object to the remainder.
Actual subquotients transport along this isomorphism, so the remainder condition
excludes every nonzero cuspidal subquotient of the ambient object.

`no_cuspidal_subquotient_of_induction_splitting` supplies that map vanishing for
normalized induction along any member of the cuspidality family. The actual
first-adjointness equivalence carries a map from a cuspidal object to a map from
its zero normalized Jacquet module. That map is zero, and injectivity of the
equivalence makes the original map zero.

`HasStandardCuspidalRemainderSplitting` specializes the input condition to
proper standard subsets, using the same family as the published `IsCuspidal`.
`no_cuspidal_subquotient_of_proper_induction_splitting` specializes the generic
exclusion to induction indexed by `I ≠ Finset.univ`.
`no_leviCuspidal_subquotient_of_proper_induction_splitting` applies that theorem
inside an actual standard Levi `M J`. Its groups are precisely
`(P (leviIndex J K)).subgroupOf (M J)` and the corresponding Levi and unipotent
subgroups. It uses the standard `normalizedInductionFunctor` for that actual
inside-Levi semidirect decomposition. The conclusion negates exactly the
published `IsLeviCuspidal`, with no flattening or group-transport premise.
Closedness of `M J` supplies its local compactness, and closedness of the ambient
unipotents supplies the inside-Levi closedness by preimage. Unimodularity of the
selected inside-Levi unipotent remains explicit.

`hasStandardCuspidalRemainderSplitting_of_rationalWholeCoproduct` consumes
`Renard.EveryObjectIsCoproductOfComponents` for the unchanged published
`rationalWholeCuspidalDecompositionProperties`. The all-cuspidal factor implies
cuspidality of its own component by testing its identity subquotient; the other
factor is exactly the required remainder property. This gives the weaker local
input for every ambient object.
`rationalNoCuspidalSubquotientProperty_of_properInduction_decomposition` takes the
published `IsRationalWholeCuspidalCategoryDecomposition` as a hypothesis at
carrier universe `max uF uV`, projects its coproduct condition, and concludes the
published `rationalNoCuspidalSubquotientProperty` for actual proper standard
induction of arbitrary smooth data of carrier universe `uV`. No irreducibility
of either inducing data or tested nonzero subquotient is required.

The family-index, group and carrier universes are independent. Induction has
carrier universe `max uG uV`, as in the published functor. Local compactness,
nonarchimedeanness, actual semidirect decompositions, closed unipotent subgroups
and unimodularity of the selected unipotent subgroup are explicit. No
irreducibility, admissibility, finite length or finite generation is assumed.
The rational bridge uses a field and topology, an actual group scheme with
affine total space and the canonical rational-point topology, local compactness
and nonarchimedeanness of its point group, a finite simple-root index, actual
semidirect decompositions and closed unipotents. It needs no valuation, local-field,
locally-finite-type, reductivity, rank or characteristic premise for this
conditional deduction.

The actual whole-category splitting remains unproved here. Applying a
rational-group splitting theorem to an inside-Levi family requires its exact
actual-family comparison, and proving the required unimodularity remains a
separate obligation. This component does not prove the full rational
cuspidal Jacquet-factor extraction statement, construct its geometric filtration,
or identify geometric grades with proper standard induction.

Worker 1553 implements this internal deduction for the extraction task; Worker 321
contributed the requested conditional exclusion interface and the connection to
standard induction inside each Levi. The mathematical inputs are the published
`IsCuspidalFor`, `IsCuspidal`, `IsLeviCuspidal`, actual first adjointness,
actual subquotient isomorphism transport, the coproduct universal property and
the unchanged rational whole-category factors. This is an internal conditional
consequence of those interfaces; it claims no new external splitting theorem.

Worker 1751's naming repair assigns explicit module-specific names to the local instances in this file. This prevents generated-name collisions when the rebuilt inertia and norm-kernel branches are imported or replayed together. Only the instance names change; their values, topology, mathematical statements and proof bodies are unchanged.
