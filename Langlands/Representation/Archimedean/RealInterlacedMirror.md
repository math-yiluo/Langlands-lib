# Interlaced induction blocks: the case `C > A` and the proof of Interlaced

Lean module: `Langlands.Representation.Archimedean.RealInterlacedMirror`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`. The final theorem is
`Langlands.Archimedean.realInterlacedInducedInducedLinkedJacquetFunctional`.

Last of the six modules `RealInterlacedJacquet`, `RealInterlacedColumns`, `RealInterlacedChain`,
`RealInterlacedEngine`, `RealInterlacedProof` and `RealInterlacedMirror` (Task 7070). It imports
`RealInterlacedProof`. It proves the case `|m(d)| < |m(e)|` (`interlaced_CA`), then the
statement itself, and then the statement II for two linked induction blocks
(`Langlands.Archimedean.realInducedInducedLinkedJacquetFunctional`).

## The theorem

`realInterlacedInducedInducedLinkedJacquetFunctional :
RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`. The statement (module
`RealInterlacedLinkedJacquetStatement`) is: for `d e : ComplexCharacterData` and `k : ℕ` with
nonzero weights, `0 < k ≤ min(|m(d)|, |m(e)|)` and
`t(d) - t(e) = ||m(d)| - |m(e)||/2 + k`, `RealLinkedJacquetFunctionalExists 4
[RealBlock.induced d, RealBlock.induced e]` holds. The proof splits on `|m(e)| ≤ |m(d)|`
(`interlaced_AC`, module `RealInterlacedProof`) and `|m(d)| < |m(e)|` (`interlaced_CA`). The
hypotheses that the weights are nonzero are not used: `0 < k ≤ min(|m(d)|, |m(e)|)` already
implies them.

## The statement II

`realInducedInducedLinkedJacquetFunctional : RealInducedInducedLinkedJacquetFunctionalStatement`
(statement in module `RealLinkedJacquetPairReduction`, Library). It is
`realInducedInducedLinkedJacquetFunctional_of_interlaced` (module `RealBlockFlatJacquet`) applied to
`realInterlacedInducedInducedLinkedJacquetFunctional`. That lemma takes a linked pair
`[induced d, induced e]` allowed by II and finds `k ≥ 1` with
`t(d) - t(e) = ||m(d)| - |m(e)||/2 + k`. For `k > min(|m(d)|, |m(e)|)` it uses the separated case
`separatedInducedInducedLinkedJacquetFunctional`. Otherwise it uses the interlaced statement.

Both `realInterlacedInducedInducedLinkedJacquetFunctional` and
`realInducedInducedLinkedJacquetFunctional` use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Outline of the proof

Write `p = |m(d)|`, `q = |m(e)|`. The position exponents are `(u₁, v₁, u₂, v₂)`, with
`A = u₁ - u₂`, `B = u₂ - v₁` and `C = v₁ - v₂` as in `RealInterlacedProof.md`. Interlacing means
`B ≥ 0`. The conclusion asks for a real Jacquet functional that kills `π(E_{p+1,p})^{k'}` at an
adjacent pair of positions with `a_p - a_{p+1} = 1 - k'`. On the standard module itself the only
adjacent pair across the two blocks is `(v₁, u₂)`, with `v₁ - u₂ = -B ≤ 0`, which gives no
binomial functional. So the proof moves exponents with Frobenius maps of explicit Jacquet
functionals (Worker 5731's `frobMap`):

1. a flat functional at one induction block (`μ = 1` or `sgn`), which keeps the exponents and
   fixes the parity of the final evaluation;
2. a tail multiplier at the middle block, which exchanges `v₁` and `u₂`;
3. a generic multiplier at the other outer block, which exchanges `u₁, u₂` (case `A ≥ C`) or
   `v₁, v₂` (case `C > A`);
4. the dichotomy (`exists_of_dichotomy`, `RealInterlacedJacquet`) at the middle block. If the
   binomial functional there is nonzero on the image, it is the desired functional. If not, the
   window of the middle block vanishes, the sign multiplier there is flat, and the binomial
   functional at the remaining linked pair gives the desired functional;
5. the nonvanishing in the second alternative (`main_value`, `RealInterlacedEngine`). Test
   vectors built from a column coordinate and self-dual Plücker coordinates stay, on `SO(4)`, in
   a space `Sm` whose top mode at the middle block is one explicit function. The vanishing
   window leaves only the top and bottom modes. The final Fourier coefficient is then an explicit
   binomial coefficient times a nonzero scalar `g`. `g ≠ 0` because otherwise the chain would
   kill an explicit mode of the test vector.

Case `A ≥ C`: flat at the block `2`, generic at the block `0`, dichotomy with `k₁ = u₁ - v₁ = p`,
final functional at the block `2` with `k₂ = C = k`. Case `C > A`: the mirror image, below.

## The case `C > A` (section CA)

Let `k ≤ p < q` and `s - t = (q - p)/2 + k`. Then `A = u₁ - u₂ = k`, `B = u₂ - v₁ = p - k`,
`C = v₁ - v₂ = q - p + k` and `u₂ - v₂ = q`.

### Test functions

* `vA = e₂` and `vB = -e₀ + i e₁ + e₃`. `colv_vA_one` and `w_one_CA` give their values at `1`:
  `w₁ = 1`, `w₂ = 1` and `w₃ = -i`.
* `values_CA_kappa`: along `r₁(t) r₂(π/2)`, `yZ h42 vA = i`, `yZb h42 vA = -i`,
  `ν₊ = i e^{-it} + i` and `ν₋ = i e^{-it} - i`.
* `values_CA_rot0`: for `T = (yZ h41 vA)^r w₊^m`, `T(r₀(θ)) = i^r (i e^{iθ} + 1)^m` and
  `T(s₃ s₂ r₀(θ)) = (-i)^r (-i e^{iθ} + 1)^m`.
* `sign_I_pow`: `(-1)^σ (-i)^r = (-1)^s i^r` when `σ + r ≡ s (mod 2)`.
* `odd_CA`: the parity condition `k + e'₀ + e'₁` odd of the final step. It is a separate lemma
  because `omega` in the large context of `engine_CA` exhausted memory.
* `coeff_kappa_CA`: if `c (-i)^r = (-1)^s i^r` and `s ≤ m`, the coefficient at `-(m - s)` of
  `t ↦ (G₊ + c G₋)(r₁(t) r₂(π/2))` is nonzero (`coeff_pair_neg_ne_zero` with the constant
  `i^r`).
* `coeff_rot0_CA`: under the same sign relation, for `g ≠ 0`, `s ≤ 1` and `m > 0`, the
  coefficient at `(1 + s) mod 2` of `θ ↦ 2π g (T(r₀(θ)) - c T(s₃ s₂ r₀(θ)))` is nonzero
  (`coeff_pair_pos_ne_zero` times `i^r`).

### The engine `engine_CA`

Data: `r + m = q + 1`, `p < m`, `m + p` odd and `σ = C mod 2`. Hypotheses:

* a real Jacquet functional `ψ₀ = ℓ_{μ₀}` at the block `0` on `[induced d, induced e]`. Its
  exponents `a₀` have the differences above, its signs are
  `e₀ = ((p + 1 + σ) mod 2, σ, (q + 1) mod 2, 0)`, and `μ₀(m) = 1`, `μ₀(-m) = (-1)^σ`;
* a multiplier `μ₁`, recurrent for `δ = 1 - B` on the class `(p + 1 + k) mod 2`, symmetric, with
  `μ₁(-(m - k mod 2)) ≠ 0`.

The chain:

1. `Ψ₀ = frobMap ψ₀`.
2. The tail step at the block `1`. The exponents become `(u₁, u₂, v₁, v₂)`.
3. `genericMultiplier C ε₂` at the block `2` (`δ = C + 1`). It has no zeros because
   `C ≡ ε₂ (mod 2)`. The exponents become `(u₁, u₂, v₂, v₁)`.
4. The dichotomy at the block `1` with `k₁ = u₂ - v₂ = q`, and the final binomial functional at
   the block `0` with `k₂ = A = k`. The flipped signs are `e' = (e₀(0), q mod 2, 1, e₀(1))`.

`main_value` is applied with the test vector of `G = Fp h42 vA vB r m`. Its sign exponents are
`(m, 0, r + m, 0)` (`isSignEq_Fp2`), and its modes are `±m` along `r₀` and `±(q + 1)` along `r₂`.
On `SO(4)`, `Ψ₀ v = G₊ + (-1)^σ G₋`. Then `hval` holds at `κ₀ = r₂(π/2)` and
`j* = -(m - k mod 2)` (`coeff_kappa_CA`), and `hfin` holds at `r_b = 0` and
`j_f = (1 + k mod 2) mod 2` (`coeff_rot0_CA`). The sign relation is
`σ + r ≡ k (mod 2)`. The arithmetic facts are proved before the main evaluation, and the
declaration uses `set_option maxHeartbeats 1000000 in`: the proof is long but elementary.

### The flat functional `exists_flat_CA`

For every `c` and `m > 0`, `ℓ_{μ₀}` at the block `0` is a real Jacquet functional with the
exponents of `[induced d, induced e]`, signs `((p + 1 + c mod 2) mod 2, c mod 2, (q + 1) mod 2, 0)`,
`μ₀(m) = 1` and `μ₀(-m) = (-1)^{c mod 2}`. For `c` even `μ₀ = 1`. For `c` odd `μ₀ = sgn`, flat
at the block `0` by `flat_sign` (`δ = p + 1`).

### The case theorem `interlaced_CA`

Let `0 < k ≤ p < q` and the linking equation hold. Take `r = (q - p) mod 2` and
`m = q + 1 - r`, so `m ≡ p + 1` and `m > p`. Take `exists_flat_CA` with `c = q - p + k`, and
`exists_tail_mult` with `B = p - k` and `j = -(m - k mod 2)`. Then apply `engine_CA`.

The module compiles with no errors or warnings.

## Provenance

The statement and its justification from the literature are in
`RealInterlacedLinkedJacquetStatement.md`. The proof here is internal to Task 7070 and does not
follow the literature route (intertwining operators and translation functors). It uses only
explicit functionals: the Library's block Jacquet functionals and multipliers
(`RealBlockJacquetFunctional`, `RealBlockMultiplier`), Worker 5731's crossing functionals and
Frobenius maps (`RealCharacterCrossing`), and the flat multipliers and test vectors of
`RealBlockFlatJacquet`.
