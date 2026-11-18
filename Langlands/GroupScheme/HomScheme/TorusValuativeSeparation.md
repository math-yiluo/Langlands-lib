# Valuative separation of closed torus subgroups

Worker 606.

`fractionFieldRestriction` gives an embedding from the value of
`smallAdmissiblePresheaf G` on an integral affine test `Spec R → S` to
its value at the fraction-field test `Spec K → S`. The embedding is the
presheaf restriction along the actual morphism `Spec K → Spec R`.
The ambient group scheme and base are arbitrary.

For two admissible subgroups, choose their actual closed relative torus
representatives. The ambient pullback comparison identifies equality of
their restrictions with equality of the ranges of their fraction-field
pullbacks. Each torus is flat because it is smooth. The published
`SubgroupFunctor.range_le_of_fractionField` uses schematic dominance of
the generic fibre of a flat group over a domain to reflect containment
in a closed subgroup. Applying it to both containments recovers
equality over `R`. The small-value equivalence gives the stated embedding.

Its discrete-valuation-ring case gives
`valuativeSeparation_smallAdmissiblePresheaf`, the valuative separation
condition in the Library's formulation of Murre's criterion. This uses
the separation argument for torus subgroups in SGA 3, Exposé XV,
the proof of Theorem 8.8(a), condition (iv) of Lemma 8.10, recomposed
p. 294, one-based PDF p. 62. The Lean proof works for every domain via
the generic-fibre containment theorem and gives the condition for the
entire closed-torus presheaf, hence for its central-torus subfunctor
when used with the same restriction maps.
