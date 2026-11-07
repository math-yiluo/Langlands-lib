# The segment-head L-factor formula from JPSS 1983, Theorem (8.2)

Author: Worker 1716. This module, in namespace `Langlands.RankinSelberg`, proves
that the Library statement `SegmentHeadLFactorStatement` (Henniart 2002, §2.6,
first display) follows from the Library statement
`SquareIntegrableLFactorStatement` (JPSS 1983, Theorem (8.2)). Theorem (8.2) is
the only premise. Everything else it uses is already proved in the Library,
including JPSS (8.1)(i).

Main result:

```lean
theorem segmentHeadLFactor_of_squareIntegrable
    (H : SquareIntegrableLFactorStatement.{uF, uV, uW, max uF uV, max uF uW})
    (H' : SquareIntegrableLFactorStatement.{uF, uW, uV, max uF uW, max uF uV}) :
    SegmentHeadLFactorStatement.{uF, uV, uW}
```

The result is conditional, because Theorem (8.2) is not proved in the
Library. When `uV = uW = uA`, both premises are the single instance
`SquareIntegrableLFactorStatement.{uF, uA, uA, max uF uA, max uF uA}`. The
assembly L-inheritance reduction (`AssemblyLSegmentReduction`) needs
`SegmentHeadLFactorStatement.{uF, uA, uA}`, and `SegmentPairPoleOrder` needs
`SegmentHeadLFactorStatement.{uF, uV, uV}`; this theorem supplies both from a
proof of (8.2).

## Provenance

- **Target.** Henniart, *Une caractérisation de la correspondance de Langlands
  locale pour GL(n)*, Bull. SMF 130 (2002) (`henniart-2002-characterization`),
  §2.6, printed page 595, first display:
  `L(s, St_n(ρ) × St_n'(ρ')) = ∏_{j=1}^{min(n,n')} L(s, ν^(n+n'-1-j) ρ × ρ')`.
  Henniart derives it from "the computations of [6]", that is, JPSS. The
  Library statement uses Lean's index `j : Fin (min n n')`, which is
  Henniart's `j - 1`, so its exponent is `n + n' - 2 - j`.
- **Premise.** Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983) (`jpss-1983-rankin-selberg`),
  Theorem (8.2), printed pages 444-445, in the Library form
  `SquareIntegrableLFactorStatement`. Here `π` is an irreducible essentially
  square-integrable component of the induction of the centered blocks
  `π₀ ⊗ α^(m/2 - i)`, `i = 0, …, m` (`centeredSegmentBlocks F m π₀`), and `σ`
  is the analogous component for `σ₀` and `n` blocks. If `t ≤ r`, then
  `L(s, π × σ) = ∏_{j=0}^{n} L(s, (π₀ ⊗ α^(m/2)) × (σ₀ ⊗ α^(n/2 - j)))`.
- **Proved Library inputs.** JPSS (8.1)(i) (`supercuspidalUnequalRankLFactor`).
  The Whittaker type of irreducible supercuspidal representations
  (`isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov`).
  Zelevinsky's essential square-integrability of segment quotients
  (`Classification.segmentSpecialEssentialSquareIntegrability`). The fact that
  a segment head is the strong socle of the decreasing induction
  (`IsSegmentHead.isIrreducibleSocle_down`). Invariance of the arbitrary-rank
  L-polynomial under opposite real twists
  (`isPadicRankLPolynomial_realPowerTwist`) and under exchanging the pair
  (`TemperedLFactorDivisibility.symmetricLPolynomial_swap`).

The new definition `segmentCenteredSeed` and the lemmas are internal proof
infrastructure. They make no claim of their own about the literature.

## Mathematical route

Let `Δ = [ρ, ν^m ρ]` (length `m + 1`, `ρ` of rank `a + 1`, represented by the
supercuspidal `A`) and `Δ' = [ρ', ν^k ρ']` (length `k + 1`, rank `b + 1`,
represented by `A'`). Let `π`, `σ` be heads of `Δ`, `Δ'`.

1. **Seed.** Take `π₀ = ν^(m/2) A`. Its centered blocks are
   `ν^(m/2 - i) ν^(m/2) A = ν^(m-i) A`, `i = 0, …, m`. These are exactly the
   blocks `ν^m A, …, νA, A` of the decreasing segment induction
   `segmentInducedDown A (m+1)`.
2. **Component.** A segment head is the irreducible strong socle of the
   decreasing induction. So it embeds as a subrepresentation, and is therefore
   an irreducible component of JPSS's centered induction of the seed. It is
   essentially square-integrable by Zelevinsky's theorem (Library).
3. **Theorem (8.2)** applies when `deg Δ' ≤ deg Δ`. With
   `σ₀ = ν^(k/2) A'` it gives `L(s, π × σ) = ∏_{j=0}^{k} Q_j`, where
   `Q_j = L(s, ν^m A × ν^(k-j) A')`.
4. **Equal ranks (`a = b`).** The degree inequality
   `(k+1)(a+1) ≤ (m+1)(a+1)` gives `k ≤ m`, so `min(m+1, k+1) = k+1` and the
   index ranges agree. Moving the twist to the first member gives
   `Q_j = L(s, ν^(m+k-j) A × A')`. Since `m + k - j = (m+1) + (k+1) - 2 - j`,
   this is Henniart's exponent.
5. **Unequal ranks (`a ≠ b`).** Every `Q_j` is `1` by JPSS (8.1)(i): the
   blocks are irreducible supercuspidal of different ranks. So `L(s, π × σ) = 1`.
   The target factors `L(s, ν^x A × A')` are also `1` by (8.1)(i), and the
   product of ones over `Fin (min (m+1) (k+1))` is `1`.
6. **Other order.** If `deg Δ' > deg Δ`, apply steps 1-5 to `(Δ', Δ)`, using
   (8.2) at the swapped universes (premise `H'`). Then transport back with the
   symmetry of the L-polynomial relation:
   `L(s, ν^x A' × A) = L(s, ν^x A × A')`, together with `min_comm` and
   `n' + n = n + n'`.

## Declarations

### Components (imported shared helper)

- `isIrreducibleComponent_of_injective`, imported from
  `Langlands.Representation.RankinSelberg.IrreducibleComponentEmbedding`: an injective intertwiner `j : π → ξ`
  from an irreducible `π` makes `π` an `IsIrreducibleComponent` of `ξ`. The
  subrepresentation is `j.range`, and the surjection is the inverse of
  `LinearEquiv.ofInjective`.

### Arbitrary-rank L-polynomials (`section Rank`)

These hold for arbitrary `ψ`, any additive Haar measure `ν` (not necessarily
self-dual), arbitrary ranks and arbitrary carriers.

- `isPadicRankLPolynomial_comm`: `IsPadicRankLPolynomial F ψ ν π σ P ↔
  IsPadicRankLPolynomial F ψ ν σ π P`. For successor ranks this is
  `symmetricLPolynomial_swap`; when a rank is `0` both sides are `False`.
- `isPadicRankLPolynomial_realPowerTwist_move`:
  `L(ν^x π × ν^y σ) = P ↔ L(ν^(x+y) π × σ) = P`.
- `isPadicRankLPolynomial_realPowerTwist_comm`:
  `L(ν^x π × σ) = P ↔ L(ν^x σ × π) = P`.

### JPSS (8.1)(i) in both orders

- `isPadicRankLPolynomial_one_of_supercuspidal`: for `ν` self-dual
  (`SelfDualHaar`) and irreducible supercuspidal `π` of `GL_(a+1)` and `σ` of
  `GL_(b+1)` with `a ≠ b`, `IsPadicRankLPolynomial F ψ ν π σ 1`. The proof
  orders the ranks. It applies `supercuspidalUnequalRankLFactor` with the
  representation of larger rank first, and gets the Whittaker type of the
  other one from the supercuspidal Kirillov theorem.

### The seed (`section Seed`)

- `segmentCenteredSeed F m ρ` (definition):
  `realPowerTwist (determinantNorm (a+1)) (m/2) ρ`, i.e. `ν^(m/2) ρ`.
- `centeredSegmentBlocks_segmentCenteredSeed`: block `i : Fin (m+1)` of
  `centeredSegmentBlocks F m (segmentCenteredSeed F m ρ)` equals
  `realPowerTwist (determinantNorm (a+1)) ((m + 1 - 1 - i : ℕ) : ℝ) ρ`. This
  is the form of block `i` of the decreasing segment induction.
- `isIrreducible_segmentCenteredSeed`, `isSupercuspidal_segmentCenteredSeed`:
  the seed of an irreducible, respectively supercuspidal, `ρ` is irreducible,
  respectively supercuspidal.
- `isIrreducibleComponent_centered_of_segmentInducedDown`: if `π` is an
  irreducible component of `(segmentInducedDown A (m+1) _).representation`,
  then it is an irreducible component of
  `canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
  (centeredSegmentBlocks F m (segmentCenteredSeed F m A.representation))`.
  The hypothesis is first restated with the same block shape
  (`BlockShape.uniform`, definitionally `succBlockShape`) and the decreasing
  blocks in explicit form. Then the block families are rewritten to agree.
  This lemma is compiled under `set_option maxHeartbeats 1000000`, a finite
  bound for the definitional unification of the two induced carriers.
- `isIrreducibleComponent_segmentInducedDown_of_isSegmentHead`: a head `π` of
  `Δ` is an irreducible component of the decreasing induction of any
  supercuspidal representative `A` of `Δ.base`. It is the strong socle there
  (`IsSegmentHead.isIrreducibleSocle_down`), and the lemma above applies.

### Main results

- `segmentHeadLFactor_of_degree_le H ψ ν Δ Δ' π σ A A' hπ hσ hA hA' hle`:
  the conclusion of `SegmentHeadLFactorStatement` for one pair with
  `Δ'.degree ≤ Δ.degree`, assuming
  `H : SquareIntegrableLFactorStatement.{uF, uV, uW, max uF uV, max uF uW}`.
  The proof follows steps 1-5 above. `Δ`, `Δ'` are destructured into ranks
  `a + 1`, `b + 1` and lengths `m + 1`, `k + 1`, and `H` is applied with
  `r = (m+1)a + m` and `t = (k+1)b + k`. The equal-rank branch reindexes by
  `Fin.cast` along `min (m+1) (k+1) = k+1`. The unequal-rank branch uses
  `IsPadicRankLPolynomial.unique` to identify each JPSS factor with `1`.
- `segmentHeadLFactor_of_squareIntegrable H H'`: `SegmentHeadLFactorStatement`.
  The proof splits on `Δ'.degree ≤ Δ.degree` and uses the swapped instance
  `H'` in the other case (step 6).

## Scope

- The theorem is conditional on JPSS Theorem (8.2) and proves nothing about
  (8.2) itself. Its statement (6), the absence of poles for square-integrable
  pairs, is not used separately.
- No other assumption is added. The quantifiers over `p`, `F`, `ψ`, `ν`,
  segments, heads and representatives are exactly those of
  `SegmentHeadLFactorStatement`.

## Lean checks

`lean_check` of `Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction`
reports 0 errors and 0 warnings. The module uses no `sorry` and no new axioms.
