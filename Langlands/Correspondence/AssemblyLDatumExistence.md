# Square-integrable data of multisegment heads

Author: Worker 1706.

This module proves the premise `MultisegmentHeadDatumExistence` of module
`AssemblyLReduction` without any hypothesis. It then removes that premise from the
reduction of `Langlands.Correspondence.AssemblyLInheritanceStatement`.

**The target statement is still not proved here.** The final theorem of this
module keeps four premises as hypotheses. Module `AssemblyLParameterPairs`
discharges two of them.

All declarations are in namespace `Langlands.Correspondence`. Throughout,
`F : PadicField.{uF} p` and `[Fact p.Prime]`. `T` is `F.canonicalTopologicalData`.

## The statement proved

`MultisegmentHeadDatumExistence.{uF, uA} F` (module `AssemblyLReduction`) says the
following. Let `Δ : Fin r → Segment.{uA, uF} T` be segments and let
`J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier)` be a Langlands
head of the multisegment `List.ofFn Δ`. Then there is a square-integrable Langlands
datum `d : SquareIntegrableLanglandsDatum.{uA, uF} T n` with two properties:

- `J` is a Langlands quotient of `d`;
- for some bijection `φ : Fin d.shape.length ≃ Fin r`, each block `d.blocks k` is a
  segment-head model of `Δ (φ k)` (`IsSegmentHeadModel`, from module
  `AssemblyEpsilonReduction`).

Being a Langlands head of `List.ofFn Δ` means that some segment product datum `d`
(`SegmentProductDatum.{uA, uF} T n`) has multisegment `List.ofFn Δ` and satisfies
`d.IsLanglandsHead J`. That predicate has three parts: the segments are
precedence-ordered, each block is a segment head of its segment, and `J` is the
irreducible head of the normalized product induction of the blocks.

The difficulty is universes. The blocks of `d` live in `max uF uA`, but the
required square-integrable datum has blocks in `uA`.

## Declarations

### Finite-occurrence matching

The module reuses `Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq`
from `Combinatorics.FiniteOccurrenceMatching`. Equal multisets of `List.ofFn f`
and `List.ofFn g` give a matching bijection of their finite index sets.
`TemperedBlockUniquenessReduction` uses this same public helper.

### `orderedSegmentSquareIntegrableConversion_of_rank`

```lean
theorem orderedSegmentSquareIntegrableConversion_of_rank {n : ℕ}
    (d : SegmentProductDatum.{max uF uA, uF} F.canonicalTopologicalData n)
    (ho : d.IsPrecedenceOrdered) (hh : d.HasSegmentHeads) :
    ∃ e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n,
      Nonempty (d.induced ≅ e.induced) ∧
        ∃ σ : Fin d.length ≃ Fin e.shape.length,
          ∀ i, ∃ h : (d.segments i).degree = e.shape.size (σ i),
            Nonempty ((h ▸ d.blocks i) ≅ e.blocks (σ i))
```

This is the Library's proved conversion
`Classification.orderedSegmentSquareIntegrableConversion.{uF, uA}`, extended to
rank `n = 0`. The Library statement requires `0 < n`.

- For `n > 0`, the theorem applies the Library conversion.
- For `n = 0`, the datum has no segments: each segment has positive degree, and
  `d.degree_sum` says the degrees sum to `n = 0`. So every index type is empty.
  The proof builds the datum `e` with the same shape and blocks as `d`. Its
  remaining fields hold vacuously. The isomorphism is `Iso.refl` and `σ` is
  `Equiv.refl`.

### `exists_smallBlock`, `smallDatum`, `smallBlockEquiv`, `smallDatumInducedEquiv`

Let `e : SquareIntegrableLanglandsDatum.{max uF uA, uF} T n`.

- `exists_smallBlock F e i`: the block `e.blocks i` is equivalent to an
  irreducible `Q : SmoothRep.{0, uF, uA}`. This is the Library theorem
  `padicIrreducibleSmoothSmallRealization.{uF, max uF uA, uA}` applied to the
  irreducible block `e.blocks i`. That theorem says every irreducible smooth
  representation of `GL_m(F)` has an equivalent irreducible realization in any
  universe.
- `smallDatum F e : SquareIntegrableLanglandsDatum.{uA, uF} T n`: the datum with the
  same shape and blocks chosen by `exists_smallBlock`. Essential square
  integrability transfers along the equivalence by
  `isEssentiallySquareIntegrable_iff_of_equiv`. The unitary exponent data
  transfers by `UnitaryExponentData.ofEquiv`, which keeps the exponent. So the
  exponents are those of `e`, and the antitonicity field is that of `e`.
- `smallBlockEquiv F e i`: the chosen equivalence from
  `(smallDatum F e).blocks i` to `e.blocks i`.
- `smallDatumInducedEquiv F e`: an equivalence of the normalized product
  inductions of `smallDatum F e` and `e`. This is the Library's cross-universe
  `normalizedProductInducedEquiv`, applied to the block equivalences.

### `isSegmentHeadModel_of_iso`

Let `P` (universe `max uF uA`) be a segment head of `Δ : Segment.{uA, uF} T`. Let
`h : Δ.degree = m` and let `B` be isomorphic to `h ▸ P`. Then every
`uA`-representation `Q` equivalent to `B` is a segment-head model of `Δ`. Proof:
`subst h`, then compose `Q ≃ B` with the inverse of the equivalence obtained
from the isomorphism (`SmoothRep.equivOfIso`).

### Main theorem

```lean
theorem multisegmentHeadDatumExistence : MultisegmentHeadDatumExistence.{uF, uA} F
```

The proof as implemented. Take `r`, `Δ`, `n`, `J` and the head hypothesis. The
head hypothesis gives a datum `d : SegmentProductDatum.{uA, uF} T n` with
`d.multisegment = List.ofFn Δ` and `d.IsLanglandsHead J`.

1. `ofFn_matching` applied to that equality gives `τ : Fin d.length ≃ Fin r` with
   `d.segments i = Δ (τ i)`.
2. `d.universeLift` has the lifted segments `Segment.{max uF uA, uF}` and the same
   blocks. It is again a Langlands head of `J`, by
   `SegmentProductDatum.universeLift_isLanglandsHead_iff` from module
   `SegmentUniverseLift`.
3. Apply `orderedSegmentSquareIntegrableConversion_of_rank` to `d.universeLift`.
   This gives a square-integrable datum `e` in universe `max uF uA`, an isomorphism
   `d.universeLift.induced ≅ e.induced`, and a bijection `σ` that matches the
   blocks of `d` with those of `e` up to isomorphism.
4. The datum is `smallDatum F e`, with permutation `σ.symm.trans τ`.
   - Quotient: `J` is an irreducible quotient of `d.universeLift.induced`, since
     the irreducible head is a quotient. Transport this along the isomorphism of
     step 3 and the inverse of `smallDatumInducedEquiv F e`, using
     `Classification.IsIrreducibleQuotient.of_equiv` twice.
   - Blocks: for an index `σ i`, the block `(smallDatum F e).blocks (σ i)` is
     equivalent to `e.blocks (σ i)`. That block is isomorphic to the transported
     segment head `d.blocks i` of `d.segments i`. So `isSegmentHeadModel_of_iso`
     gives a segment-head model of `d.segments i = Δ (τ i)`. Finally,
     `(σ.symm.trans τ) (σ i) = τ i`.

### Packaging

```lean
theorem assemblyLInheritance_of_rankinSelberg_of_blockPairs
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F
```

This is `assemblyLInheritance_of_segmentHeads_of_blockPairs` (module
`AssemblyLTwistedSupercuspidal`) with `multisegmentHeadDatumExistence` as its first
premise. The four remaining hypotheses are:

- JPSS (9.5) in product form;
- the arithmetic multiplicativity of pair L-factors over direct sums;
- the segment-head L formula of Henniart 2002, §2.6;
- the arithmetic block-pair formula.

## Provenance

The module is derived. It contains no new literature claim. The statement it
proves is the existence part of the classification of irreducible representations
by multisegments. Henniart 2002, §2.8 (printed p.596, PDF p.10) uses it to
write a Langlands quotient through square-integrable data, so that JPSS (9.5)
applies. The proof composes these:

- the Library's ordered segment conversion
  (`OrderedSegmentSquareIntegrableConversionProof`);
- the Library's small-realization theorem (`SmallRealizationProof`);
- the cross-universe induction equivalence of the Library;
- the universe lift of segment data from module `SegmentUniverseLift`.

`smallDatum` is internal infrastructure: it moves the blocks of a
square-integrable datum to the universe `uA`.
