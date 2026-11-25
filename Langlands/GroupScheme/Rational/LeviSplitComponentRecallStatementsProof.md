# Assembly of the Levi split-component recall assertions

Module `Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatementsProof`.
Namespace `Langlands.GroupScheme`.

`leviSplitComponentRecall` proves exactly
`Langlands.GroupScheme.LeviSplitComponentRecallStatements.{u}` for arbitrary
universe `u`. This is the conjunction of the three proposition definitions in
[LeviSplitComponentRecallStatements](LeviSplitComponentRecallStatements.md),
each with its existing arbitrary-field scope and hypotheses.

## Implemented proof

The proof uses conjunction introduction to pair the three published theorems
in the order of the target's right-associated conjunction:

1. [`leviSplitComponentCentralizer`](LeviSplitComponentCentralizerProof.md)
   proves `LeviSplitComponentCentralizerStatement.{u}`: the centralizer of
   the supplied embedded split component equals the image of the supplied
   embedded rational Levi as a subgroup functor, on every test scheme.
2. [`leviSplitComponentNormalizer`](LeviSplitComponentNormalizerProof.md)
   proves `LeviSplitComponentNormalizerStatement.{u}`: the two normalizer
   carriers agree over `Spec k`. Membership in either normalizer retains its
   tests after every refinement; the equality here is on rational points.
3. [`leviParabolicFinite`](LeviParabolicFiniteProof.md)
   proves `LeviParabolicFiniteStatement.{u}`: for each given rational
   parabolic and embedded rational Levi, a natural number bounds every finite
   family of rational parabolics with distinct images and that same
   embedded rational Levi. The bound is chosen before the family.

The term is `⟨leviSplitComponentCentralizer.{u},
leviSplitComponentNormalizer.{u}, leviParabolicFinite.{u}⟩`.
Each component is used at the same universe `u`; the assembly introduces no
additional hypotheses.

## Provenance

This module is an internal logical assembly of the three imported Library
proofs. Their paired Markdown files describe their respective implemented
arguments. The unchanged statement account records the recalled assertions
in Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, V.3.1 and V.3.5.1, printed pp.109–111 / PDF pp.115–117,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
and explains the arbitrary-field formalization. The conjunction packaging is
internal to the Library; no new structural argument is attributed to Renard.
