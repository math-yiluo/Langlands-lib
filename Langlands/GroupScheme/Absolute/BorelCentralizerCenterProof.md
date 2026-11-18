# Proof: the centralizer of a Borel subgroup is the centre

Worker 848.

`Langlands.GroupScheme.borelCentralizerCenter` proves exactly
`Langlands.GroupScheme.BorelCentralizerCenterStatement.{u}` in every universe.
It imports the unchanged [published statement](BorelCentralizerCenterStatement.md)
through the [centralizer reduction](BorelCentralizerCenterReduction.md).

For every algebraically closed field `k : Type u`, every smooth connected affine
group scheme `G` over `Spec k`, and every Borel subgroup `i : B ⟶ G`, it proves both
assertions of the statement:

1. For every `T : Over (Spec k)`, a point of `center B` over `T` maps under `i` into
   `(SubgroupFunctor.range i).centralizer` over `T`.
2. `(SubgroupFunctor.range i).centralizer = center G` as subgroup functors on all
   schemes over `Spec k`.

The Lean proof applies
`borelCentralizerCenter_of_homomorphismRigidity` to the published theorem
[`borelHomomorphismRigidity`](BorelHomomorphismRigidityProof.md).
That theorem discharges the reduction's entire rigidity premise in the same
universe. The resulting theorem has no additional hypotheses.

The imported reduction maps central commutation through `i` to obtain the first
assertion. For the substantive inclusion in the second assertion, conjugation
by a centralizing point of an affine test scheme fixes the base-changed Borel.
Homomorphism rigidity makes that conjugation the identity on the whole
base-changed group, so the point commutes with every group point. Affine covers
detect the commutation equality on arbitrary test schemes. The reverse
inclusion holds because a central point commutes with every subgroup point.
Thus the conclusion includes nonaffine and nonreduced test schemes.

This assembly follows the proof of Proposition 17.22 from Proposition 17.21 in
James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over
a field* (2017), printed pp.358–359, registered as
`milne-2017-algebraic-groups`. The implementation of the all-test argument is in
the imported reduction; this module supplies its proved rigidity input.
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to these two
propositions.
