# Actual two-factor extraction from a composition-length bound

Author: Worker 1277.

`Langlands.Aubert.General.twoConstituentExtraction` proves the whole exact
`TwoConstituentExtractionStatement.{uG, uV}` with no additional theorem
parameters. The imported statement pair remains unchanged.

This is an internal algebraic helper for the general rational-point rank-one
length-two proof. It applies to actual smooth representations of any
topological group over any field, with independent coefficient, group and
carrier universes. It assumes nonzeroness, reducibility and a composition-length
bound of two. It derives two actual finite-length irreducible factors and a
literal short exact sequence. It does not derive the length bound or
nonzeroness of normalized parabolic induction.

`Langlands.SmoothRep.exists_proper_subrepresentation_of_not_irreducible` uses
nonzeroness to distinguish bottom from top in the invariant-subspace lattice.
If every invariant subspace were bottom or top, this lattice would be a simple
order, contradicting reducibility. Thus there is a nonzero proper invariant
subspace `S`.

`Langlands.SmoothRep.subrepresentation_quotient_length_eq_one` applies
`Langlands.repLength_eq_add_of_exact` to the canonical short exact sequence.
Its actual subrepresentation and quotient are both nonzero, so both have
positive length. Their lengths add up to at most two in the extended natural
numbers. Each length is therefore exactly one.

`Langlands.SmoothRep.subrepresentation_quotient_shortExact` verifies injectivity
of the canonical inclusion, surjectivity of the canonical quotient map, and
equality of the inclusion's linear range with the projection's linear kernel.
These are the actual restriction and module quotient from
`Langlands.Representation.Category.Subquotients`, whose smoothness follows
from the published smoothness-transfer proofs.

`Langlands.SmoothRep.exists_two_irreducible_factors_of_length_le_two` combines
these facts. `Langlands.repLength_eq_one_iff` gives irreducibility.
`Module.length_ne_top_iff` gives finite length of each factor directly from
length one. The factors retain the original carrier universe. The
representation itself need not be supplied with a finite-length proof.

`Langlands.Aubert.General.exists_hasTwoConstituents_of_length_le_two`
specializes the coefficients to the complex numbers and packages the sequence
in the first allowed order of the published `HasTwoConstituents` predicate.
It does not assert splitting, semisimplicity, uniqueness, inequivalence of the
two factors, or any general reductive-group representation-theoretic result.

`Langlands.Aubert.General.exists_hasTwoConstituents_of_compositionLengthAtMost_two`
accepts an actual composition series with at most two factors instead of the
extended-natural length inequality. It applies
`Langlands.repLength_eq_of_hasSimpleFactors` to that series and casts its
natural-number bound into the extended natural numbers before using the
same extraction theorem. This directly accepts the form of bound in the
finite exact-family criterion; it neither proves that criterion nor supplies
any of its representation-theoretic hypotheses.

The proof is a derived algebraic argument from the actual representation
constructions and Mathlib's group-algebra module-length theory. It uses no
Langlands classification, character independence, geometric lemma,
adjointness or cuspidal-support theorem. Its application to maximal-Levi
cuspidal induction needs independently proved nonzeroness and length at most
two.
