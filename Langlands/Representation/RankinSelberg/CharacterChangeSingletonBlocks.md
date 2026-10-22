# The character-change diagonal as a singleton Levi element

Author: Worker 204.

This module connects the Whittaker character-change diagonal
`d_a = diag(a^n, ..., a, 1)` (`Langlands.Whittaker.characterChangeElement a n`
in `GL_(n+1)(F)`) and its conjugation `Langlands.Whittaker.characterChangeConj
a n` of the upper unipotent group with the singleton block geometry of
`Langlands.Group.GL.SingletonBlocks`. It identifies `d_a` with a Levi element
of the singleton shape `singletons (n + 1)`, the conjugation with the Levi
action on the singleton radical, and the block modulus of that Levi element
with the Rankin–Selberg character-change modulus
`Langlands.RankinSelberg.characterChangeModulus`.

It imports `Langlands.Group.GL.SingletonBlocks`,
`Langlands.Representation.RankinSelberg.CharacterChange` (for
`characterChangeRootExponent` and `characterChangeModulus`) and
`Langlands.Representation.RankinSelberg.AnalyticStatement` (for
`normalizedAbsoluteValue`). It contains no measure theory, Haar measure,
Jacobian or modulus-of-Haar statement, and it changes no existing
definition. All declarations live in namespace `Langlands.RankinSelberg`.
Every statement holds for every natural number `n`, including `n = 0`.

## Provenance

Internal. `characterChangeLevi` is the Levi element prescribed by the task
contract (task 15b0c237, revision 2, item 6). The theorems are direct
computations from the Library definitions named below: both `d_a` and the
block diagonal matrix of `characterChangeLevi a n` are the diagonal matrix
with entries `a^(n-i)`; both conjugations are conjugation by that matrix; and
with `t_i = a^(n-i)` the root quotient `|t_i| / |t_j|` for `i < j` is
`|a|^(j-i)`, so the singleton block modulus is `|a|` raised to
`characterChangeRootExponent n = ∑_(i<j) (j - i)`, which is the definition of
`characterChangeModulus`.

## Definition

- `characterChangeLevi (a : Fˣ) (n : ℕ) : (singletons (n + 1)).Levi F`, for
  every field `F : Type uF`, is
  `singletonLevi F (fun i : Fin (n + 1) => a ^ (n - i.val))`, the family of
  `1 × 1` scalar matrices `a^(n-i)`.

## Theorems

Character change (contract item 6), for every field `F`, `a : Fˣ` and `n`:

- `leviEmbedding_characterChangeLevi a n :
  (singletons (n + 1)).leviEmbedding F (characterChangeLevi a n) =
  characterChangeElement a n`. Proof: equality of underlying matrices
  (`Units.ext`), from `leviEmbedding_singletonLevi_val` and
  `characterChangeElement_val`.
- `upperUnipotentEquivRadical_characterChangeConj a n u`: for every
  `u : upperUnipotent (n + 1) F`,
  `upperUnipotentEquivRadical F (characterChangeConj a n u) =
  (singletons (n + 1)).leviAction F (characterChangeLevi a n)
  (upperUnipotentEquivRadical F u)`. Proof: compare underlying
  `GeneralLinear` elements; both are `d_a * u * d_a⁻¹` by
  `leviAction_apply_val`, the previous theorem,
  `upperUnipotentEquivRadical_apply_val` and `characterChangeConj_val`.

Modulus (second formula of contract item 7), for every prime `p` with
`[Fact p.Prime]`, every `F : PadicField.{uF} p` in an arbitrary carrier
universe, every `T : F.TopologicalData`, `a : F.Carrierˣ` and `n`:

- `leviModulus_characterChangeLevi_eq_pow T a n :
  T.leviModulus (singletons (n + 1)) (characterChangeLevi a n) =
  T.normalizedAbsUnits a ^ characterChangeRootExponent n` in `ℝ≥0ˣ`.
  Proof: rewrite with `leviModulus_singletonLevi`; express the exponent sum
  `∑_i ∑_j (if i < j then j - i else 0)` as `∑_i ∑_(j with i < j) (j - i)`
  (`Finset.sum_filter`) and both sides as products of powers
  (`Finset.prod_pow_eq_pow_sum`); in each factor with `i < j ≤ n`, write
  `n - i = (j - i) + (n - j)` and cancel `|a|^(n-j)`.
- `leviModulus_characterChangeLevi T a n :
  ((T.leviModulus (singletons (n + 1)) (characterChangeLevi a n) : ℝ≥0)) =
  characterChangeModulus (normalizedAbsoluteValue T) a n`. Proof: coerce the
  previous identity to `ℝ≥0` and then to `ℝ` (`Units.val_pow_eq_pow_val`,
  `NNReal.eq`, `NNReal.coe_pow`); `normalizedAbsUnits_coe` turns the left
  side into `T.normalizedAbs a ^ characterChangeRootExponent n`, which is by
  definition (`rfl`) the real value of `characterChangeModulus
  (normalizedAbsoluteValue T) a n`, since `normalizedAbsoluteValue T` has
  underlying function `T.normalizedAbs`.

## Role

With these identifications, the general block results about unipotent
radicals, Levi actions and block moduli apply to `characterChangeConj a n` on
`upperUnipotent (n + 1) F`, transported along
`upperUnipotentContinuousEquivRadical`. This is the input needed by the
unipotent character-change modulus statement of the Rankin–Selberg
development.
