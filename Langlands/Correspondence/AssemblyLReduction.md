# Reduction of assembled L inheritance to segment pairs

Author: Worker 1706.

This module is a conditional step toward
`Langlands.Correspondence.AssemblyLInheritanceStatement`
(`AssemblyLFactorStatement`). It proves that the pair L-factor compatibility of
an assembly `c` of a supercuspidal correspondence `c0` (`FullPairLCompatibility`,
module `FullLFactorCompatibility`) follows from four premises:

- Langlands heads of multisegments have square-integrable data whose blocks are
  segment heads;
- JPSS (9.5) in product form, the published statement
  `RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA}`;
- arithmetic pair L-factors are multiplicative on direct sums;
- segment heads have the L-factors of the special blocks `σ ⊗ Sp(a + 1)`.

**None of the four premises is proved here, and the module does not prove the
target statement.** The final theorem has the target statement as its
conclusion, but it keeps the four premises as hypotheses.

All definitions and theorems are in namespace `Langlands.Correspondence`.
Throughout, `F : PadicField.{uF} p` and `[Fact p.Prime]`. The universes are
those of the target: Weil–Deligne carriers in `uP`, automorphic carriers in `uA`.

The module imports `AssemblyEpsilonReduction` for the predicate
`IsSegmentHeadModel F Δ Q` and the proposition `MultisegmentHeadDatumMatching`.
`IsSegmentHeadModel F Δ Q` says that `Q`, a smooth representation of
`GL_n(F)` with carrier in `uA`, has rank `n = Δ.degree` and, after transport
along that equality, is equivalent to a representation with carrier in
`max uF uA` that is the head of the segment `Δ` (`IsSegmentHead`).

## Definitions

### `MultisegmentHeadDatumExistence.{uF, uA} F`

Let `Δ : Fin r → Segment.{uA, uF}` and let `J` (carrier `max uF uA`, rank `n`)
satisfy `Multisegment.IsLanglandsHead (List.ofFn Δ) J`. Then some
`SquareIntegrableLanglandsDatum.{uA, uF}` `d` of rank `n` has Langlands quotient
`J`, and some bijection `φ : Fin d.shape.length ≃ Fin r` makes each block
`d.blocks k` a segment head model of `Δ (φ k)`.

This is the existence half of `MultisegmentHeadDatumMatching` from
`AssemblyEpsilonReduction`, which also asks the matching for every datum with
quotient `J`. The L-factor needs only one datum, because the JPSS statement
returns the L-polynomial of the Langlands pair directly.

### `ArithmeticPairLDirectSum.{uF, uP} F`

Let `B : Fin r → LocalWeilDeligneRepresentation`, `B' : Fin t → …`, and `A`,
`A'` be Weil–Deligne representations with `⊕ B i ≅ A` and `⊕ B' j ≅ A'`
(`WeilDeligneRepresentation.Equiv` from `directSum`). Then

`arithmeticPairLFactor F [A] [A'] = ∏ i, ∏ j, arithmeticPairLFactor F [B i] [B' j]`

in `RatFunc ℂ`, where `[·]` is `WeilDeligneRepresentation.classOf`. No
positivity of `r` or `t` is required: the empty direct sum is zero, whose
L-factor is `1`, the empty product.

### `SegmentPairLCompatibility F c0`

Take the following data:

- a nontrivial `ψ` and a self-dual `ν`;
- irreducible Weil classes `σ` of rank `d + 1` and `τ` of rank `t + 1`, with
  representatives `B` and `B'`;
- segment head models `Q` of `segmentOf F c0 σ a` and `Q'` of
  `segmentOf F c0 τ b` (module `AssemblyRelation`).

Then one polynomial `P : ℂ[X]` does both of the following:

- `RankinSelberg.IsPadicRankLPolynomial F ψ ν Q Q' P` holds, that is
  `L(s, Q × Q') = 1 / P(q^(-s))`;
- `arithmeticPairLFactor F` of the published uncentered special blocks
  `WeilDeligneRepresentation.block (localNormCharacter F) B (a + 1)` and
  `… B' (b + 1)` equals `(algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹`.

These are the blocks that `IsBlockSum` uses for the assembly.

### `SupercuspidalSegmentPairLInheritance.{uF, uP, uA} F`

Every supercuspidal map `c0` with `IsSupercuspidalCorrespondence F c0` satisfies
`SegmentPairLCompatibility F c0`.

## Theorems

```lean
theorem MultisegmentHeadDatumMatching.datumExistence
    (h : MultisegmentHeadDatumMatching.{uF, uA} F) :
    MultisegmentHeadDatumExistence.{uF, uA} F
```

The existence conjunct of `h` gives a datum `d` with quotient `J`; the universal
conjunct of `h`, applied to `d`, gives the bijection.

```lean
theorem fullPairLCompatibility_of_segmentPairs
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hS : SegmentPairLCompatibility F c0)
    (hν : ∀ ψ, ∃ ν, IsSelfDualMeasure F ψ ν)
    (hc : IsAssemblyOf F c0 c) :
    FullPairLCompatibility F c
```

Proof as implemented. Fix `ψ`, ranks `r + 1` and `t + 1`, and parameters `D` and
`D'`. The existence of a self-dual measure is `hν ψ`. Fix a self-dual `ν`.
`IsAssemblyOf` gives decompositions of representatives `AD`, `AD'` of `D` and
`D'` as direct sums of special blocks `B i ⊗ Sp(m i + 1)` and
`B' j ⊗ Sp(m' j + 1)`. It also gives representatives `A` and `A'` of `c D` and
`c D'`, equivalent to Langlands heads `J` and `J'` of the multisegments of the
segments `segmentOf F c0 (σ i) (m i)` and `segmentOf F c0 (τ j) (m' j)`.

1. `hP` supplies data `d0` and `d0'` with quotients `J` and `J'`, and bijections
   `φ0`, `φ0'` from their blocks to the segments, each block being a segment
   head model of its segment.
2. `hJ`, applied to `ψ`, the self-dual measure `⟨ν, hνψ⟩`, `d0`, `d0'`, `J` and
   `J'`, gives `P` with `IsLanglandsPairLPolynomial.{uF, uA, uA} F ψ ν J J' P`,
   block polynomials `Q l l'` of the pairs of blocks of `d0` and `d0'`, and
   `P = ∏ l, ∏ l', Q l l'`. The first fact, with `A`, `A'`, `J`, `J'` and the
   equivalences, is `IsAutomorphicPairLPolynomial F ψ ν (c D) (c D') P`.
3. For each pair of blocks `(l, l')`, `hS` gives `P'` that is the rank
   L-polynomial of the two blocks and whose inverse is the arithmetic L-factor
   of the special blocks of `σ (φ0 l)` and `τ (φ0' l')`. Uniqueness of the rank
   L-polynomial (`RankinSelberg.IsPadicRankLPolynomial.unique`) gives
   `P' = Q l l'`.
4. Rewriting the parameter classes by the representatives `AD`, `AD'` and
   applying `hD` to the two block decompositions turns the arithmetic L-factor
   of `D ⊗ D'` into the product over `(i, j)` of the block-pair factors. The
   inverse of the image of `P` is the product over `(l, l')` of the inverses of
   the images of `Q l l'` (`map_prod`, `Finset.prod_inv_distrib`). Reindexing the
   first product along `φ0` and `φ0'` (`Equiv.prod_comp`) and step 3 finish the
   proof.

```lean
theorem assemblyLInheritance_of_segmentPairs
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hS : SupercuspidalSegmentPairLInheritance.{uF, uP, uA} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F
```

This applies the first theorem with `hS c0 hc0`. The self-dual measures come from
the published `IsSupercuspidalCorrespondence.exists_selfDualMeasure`
(`AssemblyEpsilonSystemHelpers`).

## Provenance

The four premise definitions are derived internal formulations. They support the
reduction and are not new literature claims. Each corresponds to a step of
Henniart 2002 (`henniart-2002-characterization`):

- `SegmentPairLCompatibility`. Henniart 2002 §2.6 (printed p.595, PDF p.9)
  defines `St_n(ρ)` as the unique irreducible quotient of
  `i(ρ, νρ, …, ν^(n-1) ρ)` and records, from JPSS, the formula
  `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')` for `j` from `1`
  to `inf(n, n')`. §2.7 (same page) sets `π_2(ρ ⊗ St_n) = St_n(π_0(ρ))` and
  deduces `L(s, π_2(σ) × π_2(σ')) = L(s, σ ⊗ σ')`. The premise is this
  L identity for the published uncentered special blocks of `AssemblyRelation`,
  attached to every `uA` model of the segment heads and stated through the
  relation `IsPadicRankLPolynomial` at every self-dual measure.
- `MultisegmentHeadDatumExistence`. Henniart 2002 §2.8 (printed p.596, PDF
  p.10) states the Langlands classification: `J(π_1, …, π_r)` is the unique
  irreducible quotient of `i(π_1, …, π_r)` for exponent-decreasing essentially
  square-integrable `π_i`. The premise asks that the precedence-ordered head of
  the segment-head product (`Multisegment.IsLanglandsHead`) be such a quotient,
  with the segment heads `St(Δ)` as blocks up to permutation, realized with
  carriers in `uA`.
- `ArithmeticPairLDirectSum`. The arithmetic counterpart of the product
  formula `L(s, π × π') = ∏_(i,j) L(s, π_i × π'_j)` of §2.8: the L-factor of a
  Weil–Deligne representation is multiplicative in direct sums, and tensor
  products distribute over direct sums.
- `SquareIntegrableDataLFactorStatement` is a published Library statement (JPSS
  1983, Theorem (9.5), in the product form of Henniart 2002 §2.8), used here
  as a hypothesis.

The theorems are derived. They prove the product formula of §2.8 on both
sides from the premises above, which gives the L identity of §2.9 (printed
p.596) and of Theorem 1.5(iii). No classification, multiplicativity or JPSS
result is proved here; each is assumed only as one of the named premises.
