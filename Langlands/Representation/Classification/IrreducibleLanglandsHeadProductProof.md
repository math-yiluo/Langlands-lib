# Tadić's Corollary A.6(ii): irreducible products of Langlands heads

Author: Worker 4988. Module
`Langlands.Representation.Classification.IrreducibleLanglandsHeadProductProof`.

## Statement proved

`Langlands.Classification.irreducibleLanglandsHeadProduct F T :
IrreducibleLanglandsHeadProduct.{uF, uV} F T`. This holds for every prime `p`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`, with independent universes `uF`
and `uV`. The proposition is the published one in `TadicExhaustionLemmasStatement`.
Let `B : BlockShape n`, let `a i : T.Multisegment` and let `π i` be smooth
representations of `GL_(B.size i)` with `(a i).IsLanglandsHead (π i)`. If the
normalized product `Π = (T.normalizedProductInductionFunctor B).obj π` is irreducible,
then `(∑ i, a i).IsLanglandsHead Π`. That is, some precedence-ordered datum of segment
heads with multisegment `∑ a_i` has `Π` as the strong irreducible head (kernel
uniqueness included) of its standard module. The theorem adds no hypothesis.

Source: M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci. ÉNS (4) 19
(1986), Corollary A.6(ii), printed p.375; literature ID `tadic-1986-unitary`. Tadić
deduces it from `L(a+b) ≤ L(a) × L(b)` (A.4, a character-continuity argument) and the
multiplicity one of `L(a+b)` in `λ(a+b)`. **The Lean proof follows a different, purely
algebraic route**, described below.

## Implemented proof

### Main theorem `irreducibleLanglandsHeadProduct`

Choose for each `i` a datum `d i` with multisegment `a i` witnessing the head relation.

- **Rank `0`** (`A6ii.rankZero`). The block shape has no blocks. The concatenation of
  the `d i` has no segments, so it is precedence-ordered vacuously and has segment
  heads. `Π` is irreducible, hence its own strong head (`isIrreducibleHead_self`). All
  rank-zero normalized products are equivalent (`rankZeroEquiv`), so `Π` is the head of
  the concatenated standard module (`IsIrreducibleHead.of_equiv`). Its multisegment is
  `∑ a i` (`concatenate_multisegment`).
- **Positive rank.** Each `d i` is reordered by decreasing chosen unitary exponents
  (`exists_sorted`). This keeps the multisegment and the standard module up to
  isomorphism, so `π i` is still the head of the sorted `(d' i).induced`. Then
  `A6ii.positiveRank` produces the merged datum. Its multisegment is that of the
  concatenation, which is `∑ a i`.

### `A6ii.positiveRank`

Let `c` be the concatenation of the sorted data `d' i`. Its segments carry the chosen
exponents `ex`, which decrease inside each `d' i`. Let `m` be a stable merge of all
segments by decreasing exponent (`exists_mergeGrouping`) and `dc = merged c m`. Then
`dc` has multisegment `∑ a i`, segment heads, and precedence order
(`merged_isPrecedenceOrdered`). By the published `orderedMultisegmentHeadExistence`,
`dc.induced` has a strong irreducible head `L`, with a surjection `q : dc.induced ↠ L`.
It remains to prove `Π ≅ L`. Then `Π` is the head of `dc.induced`
(`IsIrreducibleHead.of_targetEquiv`).

This uses the head-detecting count `HeadDetectingCount.nonempty_iso_of_count` with:

- the functor `J`: the published opposite Jacquet functor along the fine shape
  `C = fineShape c m`, which lists every supercuspidal block `ν^j A_Δ` of every segment
  `Δ` in merged order. `J` preserves injections and surjections (`A6iiCount`).
- the test representation `τ = fineAtoms`, the tensor of these `ν^j A_Δ`, where `A_Δ`
  is a supercuspidal representative of the beginning of `Δ` (`IsSegmentHead`);
- `X` = the product over `B` of the standard modules `(d' i).induced`, with
  `X ↠ Π` the product of the head maps (`productMap_surjective`);
- `I = dc.induced`, with the head map `q : I ↠ L`.

The four inputs are the following.

1. **Same composition factors** (`jhComparison`): `X` and `I` have finite length and
   the same composition factors. `X` is the concatenated standard module
   (`concatenateInducedEquiv`), and `I` is a reordering of its irreducible admissible
   blocks (`permutedProducts`, equal block lists).
2. **Count in `J I`** (`silbergerSide`): `τ` has a multiplicity `m₀ > 0` in `J I`.
   This is the published `glRelativeRegularComparison` (Silberger 1978, Lemma 5.6),
   applied with explicit data:
   - the groups of equal exponent form the coarse shape;
   - the segments within each group form the middle shape;
   - the supercuspidal blocks form the fine shape;
   - the middle blocks are the normalized square-integrable blocks
     `ν^{-e_Δ} π_Δ`.
3. **Count in `J L`** (`silbergerSide`): every irreducible quotient of `I`, in
   particular `L`, has multiplicity at least `m₀` of `τ`. The argument is second
   adjointness, as in `glRelativePositiveTotalHead` (`quotient_count_ge`).
4. **Positive count in `J Π`** (`geometricSide`). The merged order of the supercuspidal
   blocks keeps the order of the blocks coming from each factor `π i`: the merge is
   stable and the exponents decrease inside each `d' i`. So the corresponding block
   permutation is a minimal representative (`isMinimalRepresentative_permute_flatten`),
   and the whole-Levi piece of the geometric lemma (`glGeometricPieceLifting`) applies.
   Together with refined second adjointness, it exhibits `τ` as a subquotient of
   `J Π` (`geometricPiece`). Since `J Π` has finite length, the multiplicity of `τ` is
   positive.

`nonempty_iso_of_count` then concludes. If `Π ≇ L`, then `Π`, as an irreducible
subquotient of `X` and hence of `I`, would be a subquotient of `ker q`. But the count of
`τ` in `J(ker q)` is `m₀ − m₀ = 0`, while the count in `J Π` is positive.

## Supporting modules

All helper modules are internal to this proof and documented in their own Markdown:
`HeadDetectingCount`, `A6iiSorting`, `A6iiMerge`, `A6iiDatum`, `A6iiSilberger`,
`A6iiCount`, `A6iiGeometric`, `A6iiShapes`, `A6iiSegment`, `A6iiSilbergerSide`,
`A6iiGeometricSide`, `A6iiAssembly`. They use only published Library results.
