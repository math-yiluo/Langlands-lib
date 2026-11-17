# Frobenius maps for the induced–character filtration on `GL₃(ℝ)`

Module `Langlands.Representation.Archimedean.RealInducedCharacterMaps` (namespace
`Langlands.Archimedean.RealInducedCharacter`).

This is the first of five modules that together prove the filtration statement
`RealInducedCharacterFiltrationStatement` from two landing statements (see
`RealInducedCharacterFiltration.md`). It fixes notation for an induction block and builds its
*tail maps*: Frobenius maps between a standard module that contains the induction block `d`
and the standard module in which `d` is replaced by two characters. The maps are instances of
the block Frobenius maps `blockFrobMap` of module `RealBlockFrobeniusMap` (Task 7067,
Library). Their multipliers are the Library's multipliers from module
`RealBlockMultiplier`.

Notation. `d : ComplexCharacterData` is an induction block with weight `m` and exponent `t`,
and `ℓ = |m|` (`d.weight.natAbs`). `Φ^p_j f` is the block Fourier coefficient
`blockFourierCoefficient n p j f` along the rotation of the coordinates `p, p + 1`.

## Definitions

All definitions here are auxiliary and have internal provenance. None of them formalizes a
definition from the literature.

* `highIndicator ℓ k = 1` if `ℓ ≤ |k|`, else `0`. It is the multiplier that projects onto the
  modes `|k| ≥ ℓ`.
* `aExp d = t + ℓ/2` and `bExp d = t - ℓ/2`. These are the exponents at the two positions of
  the induction block `d` (see `realInducedBlockAt_eq_some` in module `RealKTypeTransport`).
* `ca d sa = charData sa (aExp d)` and `cb d sb = charData sb (bExp d)`. These are the
  characters `sgn^{s_a} |·|^a` and `sgn^{s_b} |·|^b` (`RealJacquetFrobenius.charData`).

## Lemmas

### Multipliers

* Imported `RealSwapLandingMirror.isRecurrent_congr` and `isSymmetric_congr`: the recurrence and the symmetry of a
  multiplier on the parity class `ε` depend only on `ε mod 2`. The symmetry sign may also be
  rewritten along an equation. Given `Even (k - ε')`, the proof rewrites `k - ε` as
  `(k - ε') - (ε - ε')`, a difference of two even integers.
* Imported `RealCharacterInducedPushforward.genericSeq_succ'`,
  `isRecurrent_genericMultiplier'`, and `genericMultiplier_ne_zero'`: the
  generic multiplier `genericMultiplier ν ε` solves the recurrence `IsRecurrent (ν + 1) ε` as
  soon as all denominators `ε + 2i + 1 + ν` are nonzero. If moreover `ν ≠ ε + 2m + 1` for all
  `m`, it has no zeros. These are variants of the Library lemmas `isRecurrent_genericMultiplier`
  and `genericMultiplier_ne_zero`, which assume `0 < Re ν`. The proofs use the Library's
  `isRecurrent_extend` and `extend_ne_zero_iff` together with the product formula for
  `genericSeq`.
* `isSymmetric_highIndicator`: `highIndicator ℓ` is symmetric with sign `1`.

### Setup

* `ca_parity`, `cb_parity` (simp lemmas) and `aExp_sub_bExp : aExp d - bExp d = ℓ`.

### The tail maps

Throughout, `hs : (s_a + s_b) % 2 = (ℓ + 1) % 2` and `0 < ℓ`. The lists are
`pre ++ [induced d] ++ post` and `pre ++ [c_b, c_a] ++ post`, where `c_b = cb d s_b` and
`c_a = ca d s_a`.

* `tail_parity`: `ℓ - 1 - pairParity c_b c_a` is even.
* `realRank_tail_mid`: both lists have the same rank.
* `data_tail`: the Frobenius data `IsBlockFrobData` along the block at position
  `realRank pre`, from `pre ++ [c_b, c_a] ++ post` to `pre ++ [induced d] ++ post`. Its
  multiplier is the Library's tail multiplier `tailMultiplier ℓ (pairParity c_b c_a)
  ((-1)^{s_a})`, and its symmetry sign is `(-1)^{s_a}`. The proof applies
  `IsBlockFrobData.of_mid` (module `RealBlockFrobeniusMap`). The sign and exponent fields are
  computed from `realPositionCharacter_neg_one` and `realPositionSign`. The field
  `induced_p` holds because the tail multiplier vanishes on `|j| < ℓ`
  (`tailMultiplier_ne_zero_iff`).
* `data_tailInv`: the Frobenius data in the opposite direction, with sign `((-1)^{s_a})⁻¹` and
  the pointwise inverse of the tail multiplier as multiplier. Here the target has no induction
  block at the block position, so `induced_p` is vacuous.
* `tail_tailInv`: `Tail ∘ TailInv = id` on `pre ++ [induced d] ++ post`. The proof applies
  `blockFrobMap_blockFrobMap_eq`. Wherever `μ · μ⁻¹ ≠ 1`, the tail multiplier vanishes, so
  `|j| < ℓ`. These modes of a function in the standard module vanish on `O(n)` by the block
  Fourier condition of the induction block.
* `isRecurrent_tail`: the tail multiplier solves the recurrence for
  `δ = b - a + 1 = 1 - ℓ`, by the Library's `isRecurrent_tailMultiplier`.
* `modulo_tail`: the tail map is an exact intertwiner (`IsRealIntertwinerModulo … ⊥`), by
  `isRealIntertwinerModulo_blockFrobMap`.
* `tail_surjective`: by `tail_tailInv`.
* `tail_eq_zero`: if `Φ^{realRank pre}_j g = 0` on `O(n)` for all `|j| ≥ ℓ`, then the tail
  map kills `g`. The proof compares block Fourier coefficients
  (`eq_of_blockFourierCoefficient_eq`). On the parity class, the multiplier vanishes for
  `|j| < ℓ`. Off the parity class, the coefficients vanish by
  `blockFourierCoefficient_eq_zero_of_not_even`.
* `data_high`: the Frobenius data with multiplier `highIndicator ℓ` and sign `1` from
  `pre ++ [c_b, c_a] ++ post` to `pre ++ [sgn^{s_b}|·|^a, sgn^{s_a}|·|^b] ++ post`. This is
  the projection onto the modes `|k| ≥ ℓ` that exchanges the two exponents. It is proved by
  `IsBlockFrobData.of_mid`. The target has no induction block, so `induced_p` is vacuous.
