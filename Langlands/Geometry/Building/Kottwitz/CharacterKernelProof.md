# Proof of KP Lemma 11.5.2

`Langlands.Geometry.Building.Kottwitz.characterKernel` proves the existing
`CharacterKernelStatement` at every universe `u`, with no additional hypotheses.
For every nonarchimedean local field `F` and connected reductive `F`-group `G`,
the rational-character valuation kernel `G(F)^1` is the inverse image of the
torsion subgroup of the residual invariants in `π₁(G)_I` under the constructed
`reductiveKottwitzRational`. The statement retains the given valuative relation,
its canonical valuation, the actual rational points and the actual inertia and
residual Galois actions. It applies in equal and mixed characteristic.

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Lemma 11.5.2, printed p. 431 / PDF p. 462, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The November 2024 corrections leave
this lemma unchanged. The implementation composes the published cocenter
reduction with four published proofs:

- `torusCharacterKernel` in `TorusCharacterKernelProof` proves
  `TorusCharacterKernelStatement`, the character-kernel identity for the
  restriction of the torus Kottwitz map to rational points.
- `cocenterTargetTorsion_proof` in `CocenterTargetTorsionProof` proves
  `CocenterTargetTorsionStatement`: the cocenter map on inertia targets has
  torsion kernel.
- `reductiveKottwitzFunctoriality` in `ReductiveFunctorialityProof` proves
  `ReductiveKottwitzFunctorialityStatement`, including compatibility with the
  torus Kottwitz map.
- `reductiveKottwitzDescent_assembled` in `ZExtensionKernelProof` proves
  `ReductiveKottwitzDescentStatement`, including the defining restriction law
  for the selected invariant-valued rational map.

These four proofs form `CharacterKernelInputs`. Applying its published theorem
`CharacterKernelInputs.characterKernel` gives exactly the target proposition.
The reduction chooses an actual cocenter and pulls the rational-character
valuation kernel back from its torus. Functoriality, torus compatibility and
the rational restriction law identify the Kottwitz values in the cocenter
square. A homomorphism with torsion kernel reflects finite order, and the
inclusion of residual invariants preserves and reflects finite order. The torus
identity therefore gives the required subgroup equality on `G(F)`.

This module adds only the final proof theorem. Its provenance is the composition
of these Library proofs by the already proved cocenter argument; it introduces
no new definitions or statement and changes none of the target's dependencies.
