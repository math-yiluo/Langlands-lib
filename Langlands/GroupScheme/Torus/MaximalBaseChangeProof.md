# Maximality of tori under field extension: proof

Authors: Worker 1379, Worker 1395.

`Langlands.GroupScheme.maximalTorusBaseChange` proves the published
`Langlands.GroupScheme.MaximalTorusBaseChangeStatement.{u}`
(`Langlands.GroupScheme.Torus.MaximalBaseChangeStatement`). Take fields
`k K : Type u` with `Algebra k K`, a smooth affine group scheme `G` over
`Spec k`, and a closed subgroup `i : T.toGrp ⟶ G` with `IsTorus T.toGrp`. Then
`IsMaximalTorus i` holds exactly when the base change of `i` to `Spec K` is a
maximal torus. The theorem has no hypotheses. The extension may be inseparable
or transcendental, and the fields may be finite or imperfect, of any
characteristic.

This is Milne, *Algebraic Groups* (2017), Theorem 17.82. The Lean proof
composes published Library results; it contains no new mathematics.

## Implemented proof

After introducing the data, the proof gives the two implications separately.

- **Reverse implication (maximal after extension ⇒ maximal).** This is
  `IsMaximalTorus.of_baseChange`
  (`Langlands.GroupScheme.Torus.MaximalBaseChangeReflection`), applied to the
  closedness hypothesis `hi`.
- **Forward implication (maximal ⇒ maximal after extension).** This is
  `maximalTorusBaseChangeForwardReduction`
  (`Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction`) applied to
  `k K G T i`. That reduction passes to the centralizer of the torus. It takes
  two arguments:
  1. `torusCentralizerSmooth` (`Langlands.GroupScheme.Torus.CentralizerSmoothProof`),
     a proof of `TorusCentralizerSmoothStatement`: torus centralizers are smooth
     (Milne, Corollary 13.10, centralizer half);
  2. a proof of `CentralMaximalTorusBaseChangeStatement`, the case of a central
     maximal torus. It is `centralMaximalTorusBaseChangeReduction`
     (`Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction`) applied to
     three proofs:
     - `normalSubgroupQuotient`
       (`Langlands.GroupScheme.NormalSubgroupQuotientProof`), which gives the
       quotient by a normal closed subgroup (Milne, Theorem 5.14,
       Proposition 5.18, Corollary 5.26);
     - `centralMaximalTorusQuotientStatement`
       (`Langlands.GroupScheme.Torus.CentralMaximalQuotientProof`): every
       homomorphism from a torus into the quotient by a central maximal torus
       is trivial (from Milne's proof of 17.82, using Lemma 16.43);
     - `noTorusBaseChangeReduction noTorusUnipotent`. Here
       `noTorusBaseChangeReduction`
       (`Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction`) derives
       `NoTorusBaseChangeStatement` from `NoTorusUnipotentStatement`. The latter
       is proved by `noTorusUnipotent`
       (`Langlands.GroupScheme.Torus.NoTorusUnipotent`, Milne,
       Proposition 17.81). So triviality of all torus homomorphisms survives
       base change.

`lean_check` of the module reports the axioms `propext`, `Classical.choice`
and `Quot.sound` only.
