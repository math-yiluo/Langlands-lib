# Elementary helpers for Jacquet vanishing

Author: Worker 191.

These internal algebraic helpers treat rank zero in both vanishing targets of
`JacquetInductionStatement`. The ambient general linear group of rank zero is
trivial, so all of its subgroups are equal and the identity permutation
conjugates any source Levi to any target Levi. Positivity of every block size
and its coordinate inclusion into `Fin 0` show that a rank-zero shape has no
block indices. Its empty refinement then supplies an associated target
refinement as well. Consequently the nonassociation and no-associated-refinement
hypotheses in the two respective targets are impossible at rank zero.

No representation-theoretic conclusion or positive-rank theorem is assumed.
The field and carrier universes remain independent. These are derived internal
facts about the existing constructions, not separate assertions attributed to
the literature. The positive-rank vanishing arguments remain to be assembled
from their published prerequisites.

The remaining helpers show that equality relabeling preserves a zero carrier,
and that normalized refined induction of a zero carrier is zero: its elements
are actual functions into that carrier, with covariance and smoothness imposed
by subtypes. For any geometric piece whose source refinement is proper,
quasicuspidality makes the actual refined coinvariants zero. Equality relabeling
and intersection transport preserve this carrier, and the final induction is
therefore zero. The subgroup equalities here identify the actual geometric
piece; no geometric lemma or arbitrary functor theorem is assumed.

For the final filtration argument, `subsingleton_of_isSubquotient` transfers
zero from the ambient carrier to each actual invariant subspace, its quotient,
and then across the isomorphism in `SmoothRep.IsSubquotient`.
`objectFiltrationAt` evaluates an actual natural filtration at one object;
its graded representations are definitionally the original graded functors'
values. It asserts no existence of a filtration.
