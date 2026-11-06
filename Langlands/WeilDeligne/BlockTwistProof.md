# Twisting a block

Authors: Worker 1715 (original proof draft), Worker 1743 (current-Library validation and submission).

The closing theorem `Langlands.WeilDeligneRepresentation.Blocks.blockTwist`
proves exactly the published proposition
`Langlands.WeilDeligneRepresentation.Blocks.BlockTwist.{uK, uG, uV}` from
[BlockStatements](BlockStatements.md). The universes of the field `K`, the group
`G` and the Weil carrier are independent and arbitrary. The statement pair and
the pairs it imports are unchanged.

For every field `K`, group `G`, characters `ν, χ : G →* Kˣ`, finite-dimensional
representation `σ` of `G` over `K` and length `m`, the theorem gives a genuine
Weil–Deligne pair equivalence

```
twist χ (block ν σ m) ≃ block ν (FiniteRepresentation.twist χ σ) m,
```

that is, `χ ⊗ (σ ⊗ S_m) ≅ (χ ⊗ σ) ⊗ S_m`. The proof is an internal computation
with the published definitions. It uses no characteristic or
finite-dimensionality assumption beyond those built into
`FiniteRepresentation`, and adds no claim from the original literature. The
source provenance of the identity is that of the published statement, whose
Markdown cites Tate 4.1.5 for tensor products of pairs, with a character as a
zero-monodromy pair.

## Declarations

All declarations are in the namespace
`Langlands.WeilDeligneRepresentation.Blocks`.

| Declaration | Content |
| --- | --- |
| `blockTwistEquiv ν χ σ m` | The pair equivalence `twist χ (block ν σ m) ≃ block ν (FiniteRepresentation.twist χ σ) m` whose carrier map is the identity of `σ ⊗[K] (Fin m → K)`. |
| `blockTwist` | The exact target. |

## Implemented proof

The published `block ν σ m` is `tensor (zeroMonodromy ν σ) (specialBlock ν m)`.
Both sides therefore have carrier `σ ⊗[K] (Fin m → K)`. The published `twist`
keeps the monodromy, and the twisted Weil factor still has zero monodromy, so
both monodromies are the same endomorphism `0 ⊗ 1 + 1 ⊗ N`. The monodromy
square for the identity map holds by `rfl`.

For the actions, `TensorProduct.ext'` reduces the intertwining identity to pure
tensors `v ⊗ w`. On the left the twisted action is
`χ(g) • (σ(g) v ⊗ S_m(g) w)`; on the right it is
`(χ(g) • σ(g) v) ⊗ S_m(g) w`. These agree by Mathlib's
`TensorProduct.smul_tmul'`. The theorem `blockTwist` packages
`blockTwistEquiv` as the required `Nonempty` equivalence.
