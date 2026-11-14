# Proof of the torus character-valuation kernel identity

This module proves the existing statement
`Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement`, the
Library form of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Lemma 11.1.3 (printed p. 422, PDF p. 453), together with its restriction to
rational points.

## Proof

The theorem `torusCharacterKernel` applies the published reduction
`TorusCharacterKernelInputs.torusCharacterKernel`
(`Langlands/Geometry/Building/Kottwitz/TorusCharacterKernelReduction.lean`) to
the two published input proofs:

- `torusKottwitzExistence`
  (`Langlands/Geometry/Building/Kottwitz/TorusMapProof.lean`), the proof of
  `TorusKottwitzExistenceStatement` (KP Proposition 11.1.1, printed p. 421,
  PDF p. 452);
- `normalizedIntermediateValuationStatement`
  (`Langlands/Geometry/Building/Kottwitz/TorusNormValuation.lean`), the proof of
  `NormalizedIntermediateValuationStatement`, the surjective integer
  normalization of the valuation on finite extensions of
  `UnramifiedClosure F` inside `SeparableClosure F`.

The definition `TorusCharacterKernelInputs` is exactly the conjunction of these
two statements, so the proof is a single term application.

All mathematical content is in the reduction module and in these two input
proofs. The reduction's Markdown describes the route: the norm law at a single
finite Galois splitting field `L` of `UnramifiedClosure F` gives
`κ(t)^n = π(e(ω_L(t)))` with `n = |Gal(L/K)| > 0`. Base-changed rational
characters then pair trivially with inertia-torsion cocharacters, and points of
the character-valuation kernel have trivial split valuation over `L`. This route
differs from KP's maximal-split-quotient argument, but proves the same
statement.

The development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
