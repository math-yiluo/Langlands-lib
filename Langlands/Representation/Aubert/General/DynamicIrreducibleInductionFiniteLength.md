# Finite-length embeddings for actual dynamic induction from standard inputs

Author: Worker 1212.

This internal construction retains the universal cuspidal-induction
finite-length statement at the enlarged coefficient universe, the
standard-cocharacter and standard-Levi-intersection statements, the relative
root-system statement, and uniform compactness of dynamic parabolic quotients.
It does not prove any of these inputs or the unconditional VI.6.2 target.

`FiniteLengthInductionEmbedding` records a smooth coefficient representation,
an actual injective intertwiner from induction of the original coefficient
to induction of the selected coefficient, and finite group-algebra length of
the target. The original coefficient carrier universe `uV` is independent of
the group universe `u`; the selected coefficient and induced target have
carrier universe `max (u + 1) uV`.

The constructor
`dynamicIrreducibleInductionEmbedding_of_standard_inputs` applies to the
original dynamic triple of any cocharacter in a connected reductive group
over any nonarchimedean local field. All groups use the canonical rational-point
topology. The original radical closedness and ambient local compactness and
nonarchimedean-group instances are the same as in the published target.

The implementation derives Hausdorffness of the field and its affine rational
points from the published local-field and point-topology results. It chooses
`dynamicStandardPresentation`, derives closedness of all standard radicals and
Levis, and obtains the exact inside-Levi compact quotients from the retained
uniform dynamic compactness statement. It then applies
`standardIrreducibleInductionEmbedding` with the supplied relative-root-system
input.

The standard embedding is packaged with arbitrary proofs of the standard
semidirect decomposition and radical closedness; proof irrelevance identifies
them with the proofs used in its construction. Evaluating all three
subgroup-functor equalities of the simultaneous standard presentation at the
identity test scheme gives literal equalities of the rational-point parabolic,
Levi, and radical. Rewriting these in the universally quantified embedding
data yields the desired data for the original dynamic triple. `Classical.choice`
selects the witness from `Nonempty`.

Both the source and target use the published `normalizedInductionFunctor`,
whose twist is the half Haar-modulus character on the full parabolic. The
rewriting transports this same functor; no normalization comparison is an extra
premise.

The corollary
`dynamicInductionIrreducibleFiniteLength_of_standard_inputs` descends finite
length along the constructed injective group-algebra linear map. Its conclusion
is exactly `DynamicInductionIrreducibleFiniteLengthStatement.{u, uV}`. The five
retained inputs remain hypotheses of the corollary, so this is a conditional
reduction and supplies no unconditional proof of that statement.

The provenance is internal composition of the named published constructions
and the standard embedding construction. No new literature assertion is
claimed.
