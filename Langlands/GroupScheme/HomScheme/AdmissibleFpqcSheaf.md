# Fpqc descent of actual closed torus subgroups

Author: Worker 668.

The small admissible presheaf assigns to a test scheme the actual
all-test subgroup functors represented by closed relative tori in the
pullback of the given group. It satisfies the sheaf condition for any
single flat, quasi-compact, surjective morphism of test schemes. This is
`UnramifiedFunctor.FaithfullyFlatSheaf`, the singleton fpqc clause of
Murre's representability criterion.

Matching under every pair of restrictions over the base implies matching
of all-test membership after the canonical comparison of actual ambient
pullbacks. The resulting global subgroup condition has an fpqc-closed
membership sieve, because the local conditions are given by closed
immersions. Effective fpqc descent gives a closed immersion representing
the global sieve. It carries the induced group structure. Its pullback
represents the local subgroup, so fpqc reflection of the relative torus
property makes the global subgroup admissible. The actual restriction
recovers the original local subgroup functor. Uniqueness follows from
fpqc reflection of equality of represented subgroups.

This proves the fpqc sheaf step used in SGA 3, Exposé XV, Lemma 8.10(i)
and its application to torus subgroups on recomposed page 294
(one-based PDF page 62 of the Gille–Polo recomposition of 1 December 2008,
registered source `sga3-expose-xv-raynaud-2008`). Lean works with tori
represented by closed subgroups throughout.
