# Actual factors and asymmetric Jacquet modules

This internal construction concerns actual normalized induction from a subgroup
decomposition `P = M U` in a locally compact nonarchimedean group `G`, and a
second decomposition `Q = L V`. The two Levi groups may differ. Both radicals
are closed and limits of compact subgroups. The group and inducing-carrier
universes `uG` and `uV` remain independent; the induced representation has
carrier universe `max uG uV`.

The hypotheses require that both middle Jacquet modules of the induction are
irreducible and that every irreducible actual subquotient is detected by at
least one of these two Jacquet functors. These are explicit premises, rather
than assertions established here. Finite length of the induction is not a
premise.

`two_jacquet_second_subrepresentation_subsingleton` proves that the second
Jacquet module of any nonzero proper invariant subspace is zero. The
two-Jacquet length theorem makes its actual quotient irreducible. Applying the
given detector to this quotient provides the quotient detector required by
`proper_subrepresentation_second_jacquet_subsingleton`. The latter uses first
adjointness, simplicity and actual Jacquet exactness to prove the vanishing.

`quotientSecondJacquetEquiv` constructs an equivalence from the second Jacquet
module of the whole induction to the second Jacquet module of the actual
quotient. Its map is the Jacquet image of the quotient projection, as the
`_apply` theorem records. Actual Jacquet exactness makes that map surjective
and identifies its kernel with the image of the zero second Jacquet module
of the subspace. This proves injectivity on the literal quotient carriers.

`InductionTwoJacquetFactors` records a nonzero proper actual invariant subspace
and its actual quotient, irreducibility of both factors, and all four parts
of the asymmetric Jacquet pattern. The first Jacquet module of the subspace
is equivalent to the original inducing representation. The first Jacquet
module of the quotient and the second Jacquet module of the subspace are zero.
The second Jacquet module of the quotient is equivalent to that of the whole
induction.

`inductionTwoJacquetFactors` constructs these data when the inducing object is
irreducible and its induction is reducible. Nonzero middle Jacquet module
forces the induction to be nonzero. Reducibility then supplies a nonzero
proper invariant subspace; `two_jacquet_proper_subrepresentation_irreducible`
makes it and its actual quotient irreducible. The other fields are the actual
equivalences and vanishing proofs described above. The subspace is chosen
classically; no canonical choice or splitting is claimed.

The provenance is derived from the named Library declarations. In particular,
`subrepresentationJacquetInducingEquiv` uses the actual first adjoint of the
inclusion, not a supplied Jacquet isomorphism. The length argument uses
`exactFamilyLengthBound`, compact-limit Jacquet exactness and
`subrepresentation_quotient_length_eq_one`. It uses no Langlands
classification, character independence, geometric lemma or cuspidal-support
theorem. Its irreducible-subquotient detector remains a premise.

This unit supplies the quotient side of the algebraic pattern used in the
two exponent-sign branches of the intended self-association argument. It
does not prove the simplicity or detection premises for rational cuspidal
induction, exponent inequalities, unitarizability, rational structural inputs
or `RationalRankOneSelfAssociationStatement`.
