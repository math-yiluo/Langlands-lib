# Reduction of pointed split-torus domination to the commutative case

This internal supporting module reduces the split-unipotence goal to smooth
connected affine **commutative** unipotent groups over the same ground field.
It does not prove that remaining commutative case or the exact unconditional
domination statement. All group schemes and all test schemes retain their
original ground field, including finite and imperfect fields.

`IsDerivedSubgroup.not_isIso_of_isUnipotent` chooses the published nonzero
additive character of a nontrivial affine unipotent group. The published
annihilation theorem kills its actual derived subgroup. An isomorphic derived
inclusion would cancel and make the character zero, a contradiction.

`RelativeRoot.IsFppfQuotient.isCommMonObj_of_containsCommutators` handles any
base scheme and any supplied fppf quotient with quasi-compact projection whose
full all-test kernel contains the commutators. The square of the projection is
an epimorphism. Naturality of the actual commutator morphism therefore makes
the target commutator trivial. Precomposing with pairs of arbitrary test points
proves the actual commutative group-object law. No assertion about surjectivity
on rational points is used.

`splitUnipotent_of_splitTorusDomination_of_commutative` takes the explicitly
unproved commutative case as a premise and performs strong induction on actual
Lie dimension. The zero group has a series of length zero. Otherwise the smooth
connected commutator-image representative is proper by the character argument,
hence has smaller Lie dimension. Closed-subgroup unipotence and the domination
operations apply the induction hypothesis to it. The normal-subgroup quotient
is smooth affine, connected by surjectivity, unipotent, commutative by the
previous lemma, and dominated by the same split torus after postcomposition.
The premise gives a split series for that quotient. The published extension
lemma concatenates its series with the derived-subgroup series.

`splitSeriesOfSplitTorusDominationOfCommutative` chooses the resulting length
and represented series, retaining exactly the same commutative premise.

Provenance: these are derived internal results assembled from the imported
Library's representation-based additive-character construction, actual derived
subgroup and commutator envelope, fpqc epimorphism, normal-subgroup quotient,
Lie dimension induction, and split-series extension APIs. No new source theorem
or mathematical assumption is introduced; the remaining commutative theorem is
an explicit argument of the reduction, not claimed as established.
