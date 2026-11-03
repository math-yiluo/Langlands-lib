# Unramified pullbacks on compact induction stabilizers

Authors: Worker 289 and Worker 34. Worker 34 identified the compact-stabilizer
obligation and requested this interface for the finite twist-trace construction;
Worker 289 implemented the adapter and its proofs.

This is an internal supporting construction using the published actual
`Langlands.Plancherel.unramifiedCharacters` and
`Langlands.Induction.conjOpenSubgroup`. It introduces no replacement notion of
an unramified character or inducing subgroup.

## Scope and construction

Let `M` and `H` be groups with arbitrary topologies, let
`ν : I → (M →* ℝ≥0ˣ)` be an indexed family of positive characters, and let
`r : H →* M` be continuous. The group, source and index universes are independent.
An element `χ : unramifiedCharacters ν` is the existing continuous
complex-unit-valued character whose kernel contains the actual intersection
of the kernels of all `ν i`.

`unramifiedPullbackCharacter ν r hr χ` bundles the continuous character
`h ↦ χ.val (r h)`. Its underlying homomorphism is literally
`χ.val.toMonoidHom.comp r`. The evaluation identity is definitional, and
continuity is composition of the two given continuous maps. No continuity
of `ν` is needed to construct this pullback.

Assume now the displayed hypothesis `∀ i, Continuous (ν i)`.
`compactSubgroup_le_unramifiedPullback_ker` proves that every compact subgroup
`J` of `H` lies in the kernel of this pullback. For `h ∈ J`, apply the published
`Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact` to each
continuous positive character `(ν i).comp r` on `H`. This gives
`ν i (r h) = 1` simultaneously for all `i`.
`Langlands.Plancherel.mem_commonNormKernel` therefore puts `r h` in the
actual common norm kernel. The defining property of `χ` gives `χ(r h) = 1`.
The argument works for an empty or infinite index type and needs no
topological-group, local compactness, Hausdorff or nonarchimedean instance on
`H` or `M`.

## Actual compact conjugate stabilizers

Let `G` be a topological group, `P` a closed subgroup, `K` a compact open
subgroup, and `x : G` arbitrary. Take `H = P` with its subgroup topology and
any continuous homomorphism `r : P →* M`.
The published `Langlands.Induction.isCompact_conjOpenSubgroup` gives compactness
in `P` of the actual open subgroup

```text
conjOpenSubgroup P K x = {p : P | x⁻¹ * p * x ∈ K}.
```

Applying the preceding compact-subgroup theorem proves
`conjOpenSubgroup_le_unramifiedPullback_ker`, whose conclusion is the literal
inclusion in `(χ.val.toMonoidHom.comp r).ker`.
`unramifiedPullback_eq_one_of_mem_conjOpenSubgroup` gives the pointwise
formula `χ.val (r p) = 1` for each member. There is no assumed triviality
condition, no condition on the chosen representative `x`, and no finite
double-coset cover or compactness assumption on `P \ G`.
The universes of `G`, `M` and `I` remain independent.

For an actual Levi projection, `M`, `P` and `r` can be those exact existing
groups and homomorphism. Applying the adapter still requires continuity of
that projection and of the chosen norm family. This module does not identify
an arbitrary family `ν` with all rational algebraic norm characters or
construct the rational-point topology; those are separate published
realization interfaces or consumer obligations.

## Provenance and dependencies

This is a derived adapter from published Library mathematics. It directly
imports `Induction.SurjectivityProof`, `Plancherel.UnramifiedCharacters` and
`Topology.CompactNormCharacter`. The compact-stabilizer theorem is the only
declaration used from the first import. It proves compactness by the closed
embedding `P → G` and conjugation of `K`. The compact positive-character
theorem bounds the real-valued image of a compact subgroup and uses powers
and inverses to force its values to one. The actual common-kernel membership
and character-subgroup property supply the remaining steps.
These are also the compact-containment steps used in the published
`Plancherel.NormKernelTopologyProof`; the present argument uses the more
direct compact-character theorem to avoid imposing that module's stronger
ambient topology hypotheses.

The proof uses no Langlands classification, character independence, geometric
lemma, adjointness, cuspidal-support theorem or trace regularity. It supplies
only the compact-stabilizer character condition for subsequent actual
induction calculations. Same-Levi induction independence and the whole
rational exact finite-length K0 Weyl-conjugacy target remain open.
