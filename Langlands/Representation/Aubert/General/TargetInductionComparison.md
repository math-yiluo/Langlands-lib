# Standardizing actual target-intersection induction

This internal construction compares normalized induction from an actual
geometric target intersection with normalized induction from a standard
parabolic inside the same closed coarse Levi.

`leviNormalizedInductionIsoOfEq` assumes equality of the two ambient fine
Levis, equality of the parabolics after `subgroupOf` in the coarse Levi, and
equality of the radicals after the same restriction. Identity conjugation
identifies the fine acting groups. Under those equalities, the actual
semidirect projections, closed-subgroup Haar normalization and induction
functors agree. The proof substitutes the fine Levi, identifies normalized
induction inside the coarse Levi by the other two equalities, and removes
identity conjugation using the published natural identity isomorphism.

`geometricTargetInductionComparisonIso` applies this construction to the
actual intersection functor of `GeometricK0Target`. The three structural
equalities are inputs, not consequences of minimality or Coxeter data.
All topologies are inherited from the supplied locally compact
nonarchimedean ambient group. The label, group and representation-carrier
universes are independent; induction retains the carrier saturation
`max uG uV`.

The construction is derived from the published actual parabolic functors
and identity-conjugation comparison. It supplies the target-induction
comparison needed in the termwise rewriting of Aubert's equation (1.3) in
the proof of Theorem 1.7(2), printed pp.2181–2183 / PDF pp.3–5 of
`aubert-1995-duality`. It does not prove the geometric lemma, the
intersection equalities, or the full Jacquet compatibility proposition.
