# Reduction of assembled epsilon inheritance to segment pairs

Author: Worker 1695.

This module is a conditional step toward
`Langlands.Correspondence.AssemblyEpsilonInheritanceStatement`
(`AssemblyTheorems`). It fixes one local-constant system `(eC, ε, hε)`. It then
proves that the pair epsilon compatibility of an assembly `c` of `c0`
(`FullPairEpsilonCompatibility`, module `FullFactorCompatibility`) follows from
three premises:

- Langlands data of multisegment heads consist of segment heads;
- arithmetic pair epsilon factors are multiplicative on direct sums;
- segment heads have the epsilon factors of the special blocks
  `σ ⊗ Sp(a + 1)`.

**None of the three premises is proved here.** The module does not prove the
target statement. It proves nothing about reciprocity uniqueness. In
particular, it does not show that the system belonging to `c0` has base
reciprocity component equal to a given geometric candidate `e`.

All definitions and theorems are in namespace `Langlands.Correspondence`.
Throughout, `F : PadicField.{uF} p` and `[Fact p.Prime]`. The universes are
those of the target: Weil–Deligne carriers in `uP`, automorphic carriers in `uA`.

## Definitions

### `AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F`

This is epsilon inheritance at a fixed system. It says the following for every
supercuspidal map `c0`, full map `c` and local-constant system
`(eC, ε, hε)`. Suppose `IsSupercuspidalCorrespondence F c0`, `IsAssemblyOf F c0 c`
and `SupercuspidalPairFactorCompatibility F eC ε hε c0` all hold. Then
`FullPairEpsilonCompatibility F eC ε hε c` holds.

This proposition is the interface with the reciprocity branch of the task.
That branch is meant to show that the system of `c0` is based at the given
geometric `e`. Unfolding `FullEpsilonCompatibility F e c` then needs only this
proposition with the same system. That combination is not part of this module.

### `IsSegmentHeadModel F Δ Q`

Here `Δ : Segment.{uA, uF} F.canonicalTopologicalData` and
`Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier)`. The predicate holds
when two conditions are met:

- `n = Δ.degree` via some `h`;
- after transport along `h`, `Q` is equivalent to some
  `P : SmoothRep.{0, uF, max uF uA}` with
  `F.canonicalTopologicalData.IsSegmentHead Δ P`.

`IsSegmentHead` (module `Classification/Segments`) is the irreducible head of
`i(ρ, νρ, …, ν^(m-1) ρ)` for a supercuspidal representative `ρ` of the beginning
of `Δ`. So `Q` is a model of Henniart's `St_m(ρ)` (Henniart 2002, §2.6) whose
carrier lies in `uA` rather than `max uF uA`. The small carrier is needed for the
following reason. The epsilon factor in `IsAutomorphicPairEpsilonFactor` is
`RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA}`, whose
square-integrable data have blocks with carriers in `uA`.

### `MultisegmentHeadDatumMatching.{uF, uA} F`

Let `Δ : Fin r → Segment.{uA, uF}` and let `J` (carrier `max uF uA`) satisfy
`Multisegment.IsLanglandsHead (List.ofFn Δ) J`. Then two things hold:

1. some `SquareIntegrableLanglandsDatum.{uA, uF}` of rank `n` has Langlands
   quotient `J`;
2. for every such datum `d` with Langlands quotient `J`, some bijection
   `φ : Fin d.shape.length ≃ Fin r` makes each block `d.blocks k` a segment head
   model of `Δ (φ k)`.

### `ArithmeticPairEpsilonDirectSum F eC ε hε`

Fix `ψ`, `r, t > 0`, Weil–Deligne representations `B i`, `B' j`, `A` and `A'`,
and `A ≅ ⊕ B i` and `A' ≅ ⊕ B' j`. Suppose `(e i j).1` and `(e i j).2` form an
arithmetic pair epsilon factor (`IsArithmeticPairEpsilonFactor`) of the classes
of `B i` and `B' j` for every `i` and `j`. Then
`RankinSelberg.epsilonFactorProduct e` is an arithmetic pair epsilon factor of
the classes of `A` and `A'`. The product multiplies the constants and adds the
exponents.

### `SegmentPairEpsilonCompatibility F eC ε hε c0`

Take the following data:

- a nontrivial `ψ` and a self-dual `ν`;
- irreducible Weil classes `σ` of rank `d + 1` and `τ` of rank `t + 1`, with
  representatives `B` and `B'`;
- segment head models `Q` of `segmentOf F c0 σ a` and `Q'` of
  `segmentOf F c0 τ b` (module `AssemblyRelation`).

Then one monomial `e : ℂˣ × ℤ` does both of the following:

- `RankinSelberg.IsPadicRankEpsilonFactor F ψ ν Q Q' e` holds;
- `e` is the arithmetic pair epsilon factor of the published uncentered special
  blocks `WeilDeligneRepresentation.block (localNormCharacter F) B (a + 1)` and
  `… B' (b + 1)`.

These are the blocks that `IsBlockSum` uses for the assembly.

### `SupercuspidalSegmentPairInheritance.{uF, uP, uA} F`

Let `c0` be a supercuspidal correspondence and `(eC, ε, hε)` a system with
`SupercuspidalPairFactorCompatibility F eC ε hε c0`. Then
`SegmentPairEpsilonCompatibility F eC ε hε c0` holds. This is the next
reduction step. It is not proved here.

## Theorems

```lean
theorem fullPairEpsilonCompatibility_of_segmentPairs
    {eC} {ε} {hε} {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hD : ArithmeticPairEpsilonDirectSum F eC ε hε)
    (hS : SegmentPairEpsilonCompatibility F eC ε hε c0)
    (hν : ∀ ψ, ∃ ν, IsSelfDualMeasure F ψ ν)
    (hc : IsAssemblyOf F c0 c) :
    FullPairEpsilonCompatibility F eC ε hε c
```

Proof as implemented. Fix `ψ`, ranks `r + 1` and `t + 1`, and parameters `D` and
`D'`. The existence of a self-dual measure is `hν ψ`. Fix a self-dual `ν`.
`IsAssemblyOf` gives decompositions of `D` and `D'` into special blocks
`B i ⊗ Sp(m i + 1)` and `B' j ⊗ Sp(m' j + 1)`. It also gives representatives
`A` and `A'` of `c D` and `c D'`, equivalent to Langlands heads `J` and `J'` of
the multisegments of the segments `segmentOf F c0 (σ i) (m i)` and
`segmentOf F c0 (τ j) (m' j)`.

Premise `hP` supplies data `d0` and `d0'` with quotients `J` and `J'` and
bijections from their blocks to the segments. A positive-rank block shape has a
block (private lemma `blockShape_length_pos`), so the numbers of blocks `k` and
`k'` are positive. Through the bijections, `hS` supplies for each pair `(i, j)`
an arithmetic epsilon factor `E i j` of the special blocks of `σ i` and `τ j`.
The proposed factor of `(c D, c D')` is `epsilonFactorProduct E`.

- **Representation side.** The Langlands pair epsilon factor needs, for all data
  `d` and `d'` with quotients `J` and `J'`, a block-wise factor family whose
  product is `epsilonFactorProduct E`. Here `hP` gives bijections `φ` and `φ'`
  for `d` and `d'`. The family is `E (φ l) (φ' l')`. Its product equals
  `epsilonFactorProduct E` by `RankinSelberg.epsilonFactorProduct_reindex`
  (module `RankinSelberg/LanglandsFactorDescent`). For each block pair, `hS`
  gives a monomial `e` that is the `p`-adic rank epsilon factor of the blocks.
  This `e` is also an arithmetic factor of the same special blocks. Uniqueness
  of arithmetic factors (`IsArithmeticPairEpsilonFactor.unique`, module
  `SupercuspidalEpsilonComparison`) gives `e = E (φ l) (φ' l')`.
- **Arithmetic side.** `hD` turns the factors `E i j` into a factor of the
  direct sums. The direct sums are equivalent to the representatives of `D` and
  `D'`.

```lean
theorem assemblyPairEpsilonSystemInheritance_of_segmentPairs
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hD : ∀ eC ε hε, ArithmeticPairEpsilonDirectSum F eC ε hε)
    (hS : SupercuspidalSegmentPairInheritance.{uF, uP, uA} F) :
    AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F
```

This applies the first theorem with `hS c0 eC ε hε hc0 hcompat`. The self-dual
measures come from the published
`SupercuspidalPairFactorCompatibility.exists_selfDualMeasure`
(`AssemblyEpsilonSystemHelpers`).

## Provenance

All five premise definitions are derived internal formulations. They support
the reduction and are not new literature claims. Each corresponds to a step of
Henniart 2002 (`henniart-2002-characterization`):

- `SegmentPairEpsilonCompatibility`. Henniart 2002 §2.6 (printed p.595, PDF
  p.9) defines `St_n(ρ)` as the unique irreducible quotient of
  `i(ρ, νρ, …, ν^(n-1) ρ)`. It gives the pair gamma factors of `St_n(ρ) ×
  St_n'(ρ')` as products of supercuspidal gamma factors. This "permet … de
  contrôler également les facteurs ε". §2.7 (same page) sets
  `π_2(ρ ⊗ St_n) = St_n(π_0(ρ))`, and deduces
  `ε(s, π_2(σ) × π_2(σ'), ψ) = ε(s, σ ⊗ σ', ψ)`. The premise is this epsilon
  identity. Two choices are ours: the uncentered special blocks of
  `AssemblyRelation`, and the requirement that the factor is attached to every
  `uA` model of the segment head.
- `MultisegmentHeadDatumMatching`. Henniart 2002 §2.8 (printed p.596, PDF
  p.10) states the Langlands classification. `J(π_1, …, π_r)` is the unique
  irreducible quotient for exponent-decreasing essentially square-integrable
  `π_i`, and its class depends only on the unordered family. The premise
  combines that existence and uniqueness of data with one more identification.
  The precedence-ordered head of the segment-head product
  (`Multisegment.IsLanglandsHead`) is that Langlands quotient. The blocks are
  then the segment heads `St(Δ)`, up to permutation.
- `ArithmeticPairEpsilonDirectSum`. The arithmetic counterpart of the product
  formula of §2.8: local constants of Weil–Deligne representations are
  multiplicative in direct sums, and tensor products distribute over direct
  sums.
- `IsSegmentHeadModel` is a universe-transport predicate, internal to this
  formalization.
- `AssemblyPairEpsilonSystemInheritance` is the epsilon identity of §2.9
  (printed p.596) and of Theorem 1.5(iii). It is restricted to one fixed system
  shared with `c0`.

The two theorems are derived. They prove the product formula of §2.8 on both
sides from the premises above. No classification, reciprocity uniqueness,
multiplicativity or local-constant existence result is proved here. Each of
these is assumed only as one of the named premises.
