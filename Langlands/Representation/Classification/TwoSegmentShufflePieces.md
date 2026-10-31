# Surviving geometric pieces for two segment socles

Author: Worker 1142.

This internal supporting unit computes the surviving geometric pieces of the
uniform Jacquet module of a product of segment subrepresentations on one cuspidal
line. These are the pieces of step 3 in the route for
`Langlands.Classification.TwoSegmentSocleShuffleJacquet` (Zelevinsky 1980, 1.6 with
3.1). Every result that needs Zelevinsky's 3.1 takes it as the explicit hypothesis

```text
h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T.
```

This unit proves neither 3.1 nor the shuffle Jacquet formula. It contains no
geometric-lemma filtration, no vanishing assertion and no counting. All
declarations are in `Langlands.Classification.TwoSegmentShuffle`. They are
stated for `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`
with independent universes `uF` and `uV`.

## Uniform shapes

`eq_uniform_of_size_eq hr D hD` says the following. Let `D : BlockShape (m * r)`
be a block shape with `0 < r` and `D.size i = r` for every block `i`. Then `D` is
literally `BlockShape.uniform m r hr`. Since the block sizes sum to `m * r`,
`D.length * r = m * r`, so `D.length = m`. The result then follows from
`BlockShape.ext_of_size`.

## Jacquet module of one segment

`segment_jacquet_equiv F T h31 A hA a Δ hbase Y hY D hD X hX` takes the following
data:

- a cuspidal datum `ρ` with an actual supercuspidal representative `A`;
- a real `a` and a segment `Δ` whose beginning is `ρ.twist a`;
- a segment subrepresentation `Y` of `Δ`, with carrier universe `max uF uV`;
- a shape `D` of `Δ.degree` all of whose blocks have size `ρ.rank`;
- a family `X i` of smooth representations of `GL_{ρ.rank}` with
  `X i ≅ T.segmentFactor A.obj (a + i)`, that is `X i ≅ ν^(a+i) A`.

From these it gives a `Representation.Equiv` from the normalized Jacquet module
of `Y` along `D` to `FiniteTensor.external` of the factors `X i`. Each factor is
transported to the block size `D.size i` along `hD i`.

Proof. Destructuring `Δ` and substituting `hbase` makes the rank of `Δ` equal to
`ρ.rank` by definition. `eq_uniform_of_size_eq` replaces `D` by the uniform
shape. The segment subrepresentation hypothesis supplies an actual
representative `A'` of `ρ.twist a`, and `h31` gives the equivalence with
`⊗ᵢ ν^i A'`. The published `JuxtaposedShuffle.nonempty_cast_iso` identifies
`ν^i A'` with `X i`, using `ν^i ν^a A ≅ ν^(i+a) A` and the fact that `A'` and the
twist `ν^a A` lie in the same supercuspidal class. The published
`FiniteTensorFiltration.externalCongr` then replaces the factors.

## The piece equivalence

Fix `m`, a datum `d : T.SegmentProductDatum.{uV, uF} (m * ρ.rank)`, reals
`a j` with `(d.segments j).base = ρ.twist (a j)`, and the hypothesis that each
block `d.blocks j` is a segment subrepresentation of `d.segments j`. Write
`C = BlockShape.uniform m ρ.rank ρ.rank_pos`, and take:

- a permutation `w` that is a minimal representative for `(d.shape, C)`;
- refinements `S` of `d.shape` and `R` of `C`;
- the source and target intersection equalities `hS` and `hR`;
- `hdiv : ∀ j i, ρ.rank ∣ (S j).size i`.

Write `t(j, i) = ShuffleRefinement.refinementTargetIndex ρ.rank_pos d.shape w S j i`.
This is the target block that receives piece `i` of source block `j`. Let `X`
be a family of smooth representations of `GL_{ρ.rank}` indexed by `Fin m` with

```text
hX : ∀ j i, Nonempty (X (t(j, i)) ≅ T.segmentFactor A.obj (a j + i)).
```

`pieceEquiv F T h31 A hA d a hbase hsub w hw S R hS hR hdiv X hX` is an actual
`Representation.Equiv`. Its source is the geometric piece
`(geometricPieceFunctor T d.shape C w S R hS hR).obj (FiniteTensor.externalSmoothObject d.blocks)`.
Its target is `FiniteTensor.external (fun t => (X t).representation)`, a
representation of `C.Levi`. It is the composite of five equivalences:

1. `Geometric.wholeLeviGeometricPieceEquiv`. Divisibility makes the conjugated
   flattened Levi equal to the Levi of `C`, by
   `ShuffleRefinement.conjugatesLevi_flatten_uniform`. So the piece is the
   transport along `w` of the normalized refined Jacquet module of
   `⊗ⱼ d.blocks j`, pulled back to the flattened Levi.
2. `RefinedJacquetTensor.jacquetEquiv`. The refined Jacquet module of the
   external tensor is the external tensor of the Jacquet modules
   `r_{S j}(d.blocks j)`. `segment_jacquet_equiv` identifies the module for
   block `j` with `⊗ᵢ X(t(j, i))`. Each factor is cast to the size `(S j).size i`
   along `ShuffleRefinement.source_size_eq_of_dvd`. Tensor congruence then gives
   the nested tensor `⊗ⱼ ⊗ᵢ X(t(j, i))` on the refined Levi.
3. An identity equivalence. Pulling back along the inverse of
   `refinedLeviEquiv` and then along `flattenedLeviEquiv` is the pullback along
   `flattenedLeviProductEquiv`. The underlying linear map is the identity, and
   the intertwining identity is checked pointwise by `simp`.
4. `CuspidalSupport.transportEquiv` transports the composite of 2 and 3 along `w`.
5. The inverse of `ShuffleRefinement.uniformRefinementTensorEquiv`. It identifies
   this transported nested tensor with `⊗ₜ X t`.

The definition carries `set_option maxHeartbeats 1000000`, a finite limit.

## Two segment socles

`surviving_piece_equiv` is the two-block case in the coordinates of the target
statement. Take `d : T.SegmentProductDatum.{uV, uF} ((m₀ + m₁) * ρ.rank)` with
`h₂ : d.length = 2`, `d.HasSegmentSocles`, segment beginnings `ρ.twist a₀` and
`ρ.twist a₁`, and the block sizes `h₀`, `h₁` equal to `m₀ * ρ.rank` and
`m₁ * ρ.rank`. Take also a minimal representative
`w : MinimalRepresentatives d.shape C`, refinements `S` and `R` with
`IsIntersectionRefinement` proofs `hS` and `hR`, and `hdiv`. Then the geometric
piece of `w` (with the equalities `hS.2.1` and `hR.2.1`) is equivalent to the
shuffle tensor

```text
FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos
  (ShuffleRefinement.refinementShuffle ρ.rank_pos d.shape h₂ h₀ h₁ w.val S hS.2.1
    w.property hdiv).val a₀ a₁).
```

Proof. Every index `j : Fin d.length` is `Fin.cast h₂.symm 0` or
`Fin.cast h₂.symm 1`. Set `a j = a₀` at the first block and `a₁` otherwise.
`IsSegmentSocle.isSegmentSubrepresentation` turns the socle hypotheses into
segment subrepresentations. Apply `pieceEquiv` with `X` the shuffle factors.
The required isomorphisms `hX` are equalities of exponents, given by the
published `ShuffleRefinement.shuffleExponent_refinementTargetIndex_zero` and
`ShuffleRefinement.shuffleExponent_refinementTargetIndex_one`. They are realized
by `eqToIso`.

No finite length, irreducibility, genericity, linkage or distinctness premise
is added. The reals `a₀`, `a₁` are arbitrary, and the segments may be equal,
repeated or linked.

## Provenance and dependency audit

The provenance is internal. The unit is coordinate and representation algebra
over the published inputs below, conditional on Zelevinsky 1980, 3.1 (printed
pp. 180–181), which enters only as the hypothesis `h31`. The surviving-piece
identification follows the description of the geometric lemma in Zelevinsky
1980, 1.6 (printed pp. 171–172), but no geometric-lemma theorem is used here.

| Input | Origin and role | Independence |
| --- | --- | --- |
| `SegmentSubrepresentationFullJacquet` | Statement module `Classification.SegmentFullJacquetStatement` (statement task ed48ae06-964c-4c84-9e62-978f5a953ca7). Only the proposition, as hypothesis `h31`. | A `Prop` definition. Its proof task b331611c-526d-4925-87fe-ea67ed6e6fed is the intended input of the parent task. |
| `JuxtaposedShuffle.nonempty_cast_iso` | Supporting unit `Classification.JuxtaposedRefinementTools`, published under task 0c90f7e4-78fa-43fd-8736-238bb3e8617d. Twist composition and supercuspidal-class transport. | It imports only `Segments`, `Parabolic.OrderedProductRegroupingProof` and `CuspidalSupport.MinimalJacquetProof`. It is not the exact proof of `JuxtaposedSegmentSocleReverseProductStructure` and assumes none of its conclusions. |
| `refinementTargetIndex`, `source_size_eq_of_dvd`, `conjugatesLevi_flatten_uniform`, `refinementShuffle`, `shuffleExponent_refinementTargetIndex_zero/one`, `uniformRefinementTensorEquiv` | Worker 167's finite supporting units `UniformRefinementCoordinates`, `UniformRefinementCombinatorics`, `UniformRefinementShuffleRealization`, `UniformRefinementLeviTransport`, `TwoSourceShuffleLabels` and `UniformTargetBlockLabels`, published under task 0c90f7e4. Coordinates, labels, conjugacy and the tensor transport. | Finite coordinate and tensor algebra from explicit intersection, divisibility and minimality hypotheses. No Jacquet formula is assumed. They import the target statement module only for the definition of `shuffleExponent`. |
| `wholeLeviGeometricPieceEquiv` | `Geometric.WholeLeviPieceTransport` (task 66ee5306-1968-41ce-90ce-88486e2a8c3f). The piece is a transported refined Jacquet module. | Unwinds the definition of `geometricPieceFunctor` and needs no cuspidality or vanishing premise. It imports `SegmentEdgeJacquetReduction`, a supporting unit of the intended input task b331611c, which assumes no excluded result. |
| `RefinedJacquetTensor.jacquetEquiv`, `FiniteTensorFiltration.externalCongr/compCongr`, `flattenedLeviEquiv`, `flattenedLeviProductEquiv`, `refinedLeviEquiv` | `Parabolic.RefinedJacquetTensor`, `Tensor.ProductFiltration`, `Geometric.FlattenedLevi`. | Coinvariant and tensor algebra and product reindexing. |
| `CuspidalSupport.transportEquiv` | `CuspidalSupport.LeviAssociation` (task 53969569-6b54-45b3-a1f8-89f1fe96a1f8). Transport of an equivalence along a Levi conjugation. | Uses the same linear equivalence. The association theorems of the module are not used. |
| `IsSegmentSocle.isSegmentSubrepresentation`, `segmentFactor` | `Classification.Segments`. | Definitions and a direct consequence of them. |

The recursive project import closure has 181 modules. Its `Classification`
modules are `ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`,
`Essential`, `JuxtaposedRefinementTools`, `LanglandsData`,
`SegmentEdgeCombinatorics`, `SegmentEdgeJacquetReduction`,
`SegmentEdgeJacquetStatement`, `SegmentFullJacquetStatement`, `Segments`,
`Supercuspidal`, `SupercuspidalTwist`, `Tempered` (definitions of temperedness),
`TwoSegmentSocleShuffleJacquetStatement` (definitions and the target
proposition, not a proof), `TwoSourceShuffleLabels`,
`UniformRefinementCombinatorics`, `UniformRefinementCoordinates`,
`UniformRefinementLeviTransport`, `UniformRefinementShuffleRealization` and
`UniformTargetBlockLabels`. The other proof modules in the closure are lower
`CuspidalSupport`, `Filtration`, `Geometric` (Weyl representatives and
intersections), `Induction`, `Parabolic`, `Smooth`, `Twist` and
`LocalField.Normalization` results.

The closure contains no statement or proof of any exclusion of the parent task.
That covers the reverse-product structure theorems (juxtaposed, linked and the
quotient-Hom), linked pair reducibility, `SegmentSocleProductIrreducibility`,
`AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
`LinkedSegmentSocleGluing`, `OrderedMultisegmentSocleExistence`, the exhaustion
and coverage results, tempered block uniqueness,
`SquareIntegrableLanglandsClassification`, `SegmentHeadProductIrreducibility`
and derivatives. The units published under task 0c90f7e4 are its finite
supporting infrastructure, not its exact proof. Since they do not import this
unit, there is no circularity.
