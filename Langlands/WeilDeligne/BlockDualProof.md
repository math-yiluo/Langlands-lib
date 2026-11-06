# The dual of a block

Authors: Worker 1715 and Worker 1745.

Worker 1715 supplied the initial complete draft; Worker 1745 checked it against
the task’s Library base and prepared the proof contribution.

The closing theorem `Langlands.WeilDeligneRepresentation.Blocks.blockDual`
proves exactly the published proposition
`Langlands.WeilDeligneRepresentation.Blocks.BlockDual.{uK, uG, uV}` from
[BlockStatements](BlockStatements.md). The universes of the field `K`, the group
`G` and the Weil carrier are independent and arbitrary. The statement pair and
the pairs it imports are unchanged.

For every field `K`, group `G`, character `ν : G →* Kˣ`, finite-dimensional
representation `σ` of `G` over `K` and length `m`, the theorem gives a genuine
Weil–Deligne pair equivalence

```
dual (block ν σ m) ≃ block ν (FiniteRepresentation.twist (ν^(1-m)) (FiniteRepresentation.dual σ)) m,
```

that is, `(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`, with the integer power `1 - m`.
The proof is an internal computation with the published definitions and the
published tensor-duality equivalence. It uses no characteristic assumption and
adds no claim from the original literature. The source provenance of the
identity is that of the published statement, whose Markdown cites Henniart 2002
§2.3 (`St_n^∨ ≅ ν^(1-n) ⊗ St_n`) and §2.2 (duals distribute over tensor
products).

The intermediate equivalence `specialBlockDualEquiv ν m` has exactly the type
inside the published proposition `SpecialBlockDual` from the same statement
module. This module does not state a theorem for that proposition.

## Declarations

`S_m` is the published `specialBlock ν m`: carrier `Fin m → K`, the coordinate
vector `e_j = Pi.single j 1` has weight `ν^j` (`Special.action`), and the
raising monodromy `N = Special.raising K m` sends `e_j` to `e_(j+1)` and kills
`e_(m-1)`. Write `rev i = m - 1 - i` (`Fin.rev`). The dual pair `A^∨` is the
published `dual A`: action `ℓ ↦ ℓ ∘ A(g⁻¹)` and monodromy `ℓ ↦ -(ℓ ∘ N)`.

| Declaration | Content |
| --- | --- |
| `Special.action_single ν m g j` | `Special.action ν m g e_j = ν(g)^j • e_j`. It is the published `action_basisVector`, rewritten from `basisVector K j` to `Pi.single j 1`. |
| `Special.raising_single m j` | `Special.raising K m e_j` is `e_(j+1)` if `j + 1 < m`, and `0` otherwise. |
| `Special.signReverse K m` | The linear automorphism `w ↦ (i ↦ (-1)^(rev i) · w(rev i))` of `Fin m → K`, with inverse `u ↦ (j ↦ (-1)^j · u(rev j))`. |
| `Special.dualEquiv K m` | The linear equivalence `Module.Dual K (Fin m → K) ≃ (Fin m → K)`: coordinates in the dual of the standard basis, followed by `signReverse`. |
| `Special.dualEquiv_apply m ℓ i` | `dualEquiv K m ℓ i = (-1)^(rev i) · ℓ(e_(rev i))`. |
| `Special.units_inv_pow_eq u i k` | For a unit `u`, `(u⁻¹)^k = u^(1 - (i + 1 + k)) · u^i`, with an integer exponent. |
| `specialBlockDualEquiv ν m` | The pair equivalence `dual (specialBlock ν m) ≃ twist (ν^(1-m)) (specialBlock ν m)` with carrier map `Special.dualEquiv K m`. |
| `tensorTwistEquiv ν χ τ B` | For a finite-dimensional representation `τ` and a pair `B`, the pair equivalence `tensor (zeroMonodromy ν τ) (twist χ B) ≃ tensor (zeroMonodromy ν (FiniteRepresentation.twist χ τ)) B` with the identity carrier map. |
| `Blocks.blockDualEquiv ν σ m` | The pair equivalence of the target, as a composite of three equivalences. |
| `Blocks.blockDual` | The exact target. |

The first six declarations are in the namespace
`Langlands.WeilDeligneRepresentation.Special`. `specialBlockDualEquiv` and
`tensorTwistEquiv` are in `Langlands.WeilDeligneRepresentation`, and the last
two are in `Langlands.WeilDeligneRepresentation.Blocks`.

## Implemented proof

**Coordinate lemmas.** `raising_single` is checked coordinatewise from the
published `raising_apply`, by cases on `0 < k`, `j + 1 < m` and `k = j + 1`.
`dualEquiv_apply` is Mathlib's `Module.Basis.dualBasis_equivFun` for the
standard basis `Pi.basisFun`, whose vectors are `Pi.single i 1`. The two
inverse laws of `signReverse` hold because `rev (rev i) = i` and
`(-1)^a · (-1)^a = 1`. `units_inv_pow_eq` is a computation in the group of units
with integer powers.

**The dual special block.** Let `ℓ` be a functional on `Fin m → K` and fix a
coordinate `i`; put `k = rev i`, so `m = i + 1 + k`.

- Action. The left side is `dualEquiv (ℓ ∘ S_m(g⁻¹)) i`. By `dualEquiv_apply`
  and `action_single` it equals `(-1)^k · ν(g⁻¹)^k · ℓ(e_k)`. The right side is
  the twisted action `ν(g)^(1-m) · ν(g)^i · dualEquiv ℓ i`, which equals
  `ν(g)^(1-m) · ν(g)^i · (-1)^k · ℓ(e_k)`. Since `ν(g⁻¹) = ν(g)⁻¹`,
  `units_inv_pow_eq` with `m = i + 1 + k` closes the identity.
- Monodromy. The left side is `dualEquiv (-(ℓ ∘ N)) i`, which equals
  `-(-1)^k · ℓ(N e_k)`. The right side is `N (dualEquiv ℓ) i`. If `0 < i`, then
  `k + 1 < m`, so `N e_k = e_(k+1)`. Moreover `rev (i - 1) = k + 1`, and both
  sides equal `(-1)^(k+1) · ℓ(e_(k+1))`. If `i = 0`, then `k = m - 1`, so
  `N e_k = 0`, and both sides vanish.

The twisted special block keeps the monodromy `N`, so this is
`specialBlockDualEquiv`. Its inverse sends `e_i` to
`(-1)^(m-1-i) · e*_(m-1-i)`, which is the statement Markdown's basis
`f_i = (-1)^i e*_(m-1-i)` multiplied by the constant sign `(-1)^(m-1)`.

**Moving the twist.** In `tensorTwistEquiv`, both sides have carrier `τ ⊗[K] B`
and monodromy `0 ⊗ 1 + 1 ⊗ N_B`, since the published `twist` keeps the
monodromy. The monodromy square holds by `rfl`. On pure tensors the two actions
are `τ(g) v ⊗ (χ(g) • B(g) w)` and `(χ(g) • τ(g) v) ⊗ B(g) w`. These agree by
Mathlib's `TensorProduct.smul_tmul`, and `TensorProduct.ext'` extends the
identity to the whole carrier.

**The block.** The published `block ν σ m` is
`tensor (zeroMonodromy ν σ) (specialBlock ν m)`. `blockDualEquiv` composes:

1. the inverse of the published `tensorDualEquiv (zeroMonodromy ν σ) (specialBlock ν m)`,
   which identifies `dual (block ν σ m)` with the tensor product of the duals of
   the two factors;
2. the published `tensorEquiv` of the published `dualZeroMonodromyEquiv σ`,
   `dual (zeroMonodromy ν σ) ≃ zeroMonodromy ν σ^∨`, and of
   `specialBlockDualEquiv ν m`;
3. `tensorTwistEquiv ν (ν^(1-m)) σ^∨ (specialBlock ν m)`, which moves the twist
   onto the Weil factor.

The target of the composite is
`tensor (zeroMonodromy ν (twist (ν^(1-m)) σ^∨)) (specialBlock ν m)`. By
definition this is `block ν (FiniteRepresentation.twist (ν^(1-m)) (FiniteRepresentation.dual σ)) m`.
The theorem `blockDual` packages `blockDualEquiv` as the required `Nonempty`
equivalence.

The construction also covers length zero: `Fin 0` is empty, so all coordinate
extensionality arguments are vacuous and the same equivalences apply. In
characteristic two, the alternating signs are all `1`; the inverse laws still
use the valid identity `(-1)^2 = 1`, and the monodromy calculation remains valid.
