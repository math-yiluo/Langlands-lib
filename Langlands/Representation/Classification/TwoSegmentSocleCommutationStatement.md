# Commutation of two unlinked segment socles

Author: Worker 219. The exact interface and independence requirements were
supplied by task `426911b4-6620-413f-8065-04b25287f3bd`, published in
coordination with Workers 491 and 494.

`Langlands.Classification.TwoSegmentSocleCommutation.{uF,uV} F T` is a
Prop-valued definition, not a proof. It asks for an actual categorical
isomorphism between the normalized induced products of two supplied segment
socles taken in the two orders.

## Exact proposition

Fix any `p : ℕ` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The declaration installs `T.topology`.
The field universe `uF` and carrier parameter `uV` are independent. Writing
`v = max uF uV`, the segments and the actual smooth complex representation
blocks in the datum use the specified `T.SegmentProductDatum.{v,uF}` universe.

For every `n : ℕ`, every `d : T.SegmentProductDatum.{v,uF} n`, and every
`h₂ : d.length = 2`, assume `d.HasSegmentSocles` and

```text
¬ (d.segments ⟨0, by omega⟩).IsLinked (d.segments ⟨1, by omega⟩).
```

Both index bounds, and the bound for the adjacent swap, are justified using
`h₂`. Let `σ = d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)`.
The conclusion is exactly

```text
Nonempty (d.induced ≅ (d.permute σ).induced).
```

The isomorphism is in the actual smooth complex representation category of
`GL_n(F)`, so it consists of invertible equivariant complex-linear maps. By
the published `SegmentProductDatum.permute_induced`, its right side is also

```text
(T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
  (fun i => d.blocks (σ i)).
```

The permutation sends a new position `i` to the original label `σ i`.
`SegmentProductDatum.permute` definitionally retains each supplied block,
with its segment and degree. It does not choose replacement representatives
or discard occurrences. Repeated and equal segments are allowed; under the
existing definition a segment is not linked to itself.

There is no order, precedence, pairwise-criterion, genericity, unitarity,
whole-product irreducibility, finite-length, classification, or supplied
commutation premise. Every natural ambient rank is quantified. Rank zero is
vacuous here: the datum has two segments, each of positive degree, and their
degrees sum to the ambient rank. The conclusion is a categorical isomorphism
of the two actual normalized induced objects. It is not an equality of
composition-factor multisets or of classes in a Grothendieck group. This
statement concerns exactly two factors; swapping adjacent factors inside a
longer product requires a separate lifting argument.

## Conventions

The unchanged imported definitions use normalized induction from the standard
upper block parabolic, positive half-modulus covariance and right translation,
with `ν = |det|_F` and residue normalization `|varpi|_F = q^(-1)`.
`HasSegmentSocles` states that each supplied block `d.blocks i` satisfies
`T.IsSegmentSocle (d.segments i)`. For `Δ = [ρ, νρ, …, ν^(m-1)ρ]` this says
the block is an irreducible subrepresentation of the increasing cuspidal
induction `ρ × νρ × ⋯ × ν^(m-1)ρ` of a represented base, and that every
injective intertwining map into that product from an irreducible
representation on a carrier of the same universe has the same image. This is
Zelevinsky's `⟨Δ⟩`. It is not the special head of that product, and the
witness does not assert that a socle has been constructed for every segment.

`Segment.IsLinked` is Zelevinsky's linkage: neither support contains the
other, and their union is the support of a segment.

## Original source and derived provenance

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Registered source: `zelevinsky-1980-induced-ii`; SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

- §3.1, printed pp.180–181 (PDF pp.17–18), defines `⟨Δ⟩` as the irreducible
  representation attached to the increasing orientation, equivalently the
  unique irreducible submodule of `ρ × νρ × ⋯ × ρ'`.
- §4.1, printed p.184 (PDF p.21), defines linked segments. Theorem 4.2 on
  the same page states that `⟨Δ₁⟩ × ⋯ × ⟨Δ_r⟩` is irreducible exactly when
  no two of the segments are linked. Its proof, §§4.3–4.6, runs through
  printed p.186 (PDF p.23).
- Theorem 1.9, printed p.174 (PDF p.11), states that for finite-length
  `π₁, π₂` the products `π₁ × π₂` and `π₂ × π₁` have the same composition
  factors.
- Proposition 6.4(1), printed p.189 (PDF p.26), states that products of
  segment socles whose ordered sequences differ by transposing two unlinked
  neighbours are equivalent. Its proof cites associativity, commutativity
  (§§1.7, 1.9) and Theorem 4.2.

This interface is the two-factor case of Proposition 6.4(1), derived from
the source as follows. For unlinked `Δ₁, Δ₂`, Theorem 4.2 applied to both
orders makes `⟨Δ₁⟩ × ⟨Δ₂⟩` and `⟨Δ₂⟩ × ⟨Δ₁⟩` irreducible. Theorem 1.9 says
they have the same composition factors. Two irreducible representations
with the same single composition factor are equivalent. The interface
expresses equivalence as an actual categorical isomorphism, and it retains
the particular blocks supplied in `d`. Theorem 1.9 alone gives no product
isomorphism; the irreducibility of both orders is essential.

The pages listed above were read for this contribution. No source-specific
`notes/errata/zelevinsky-1980-induced-ii.md` was present in the supplied
public notes. The published guidance distinguishing segment heads from
segment socles was respected.

## Intended independent proof route

A future proof must construct an actual isomorphism for the supplied blocks.
It is intended to combine three independently proved inputs:

1. Irreducibility of both orders. The two-segment case of the sufficient
   direction of Theorem 4.2, applied to `d` and to `d.permute σ`. The latter
   keeps `HasSegmentSocles` by the published
   `SegmentProductDatum.HasSegmentSocles.permute` in
   `Classification.SegmentSocleProductData`. The pairwise unlinked
   hypothesis on the two-element multisegment follows from the premise and
   the published `Segment.IsLinked.symm` and `Segment.not_isLinked_self`.
   That statement uses a rank of the form `m + 1`; here the rank is positive
   because the two segment degrees are positive. The
   intended owner is the proof successor of
   `Langlands.Classification.UnlinkedSegmentSocleProductIrreducible`
   (statement task `16045335-62c9-4da7-b38f-88579104274b`). The full
   criterion `Langlands.Classification.SegmentSocleProductIrreducibility`
   (proof task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`) would also suffice
   but is not needed.
2. Composition-factor commutativity for two irreducible factors, the
   irreducible case of Theorem 1.9. The intended owner is
   `Langlands.Classification.TwoFactorProductConstituentCommutativity`
   (task `1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9`), used at shape `d.shape`,
   family `d.blocks` and carrier parameter `max uF uV`. Its swapped side is
   literally `(d.permute σ).induced`. Each block is irreducible because the
   socle witness includes irreducibility.
3. Passage from equal Jordan–Hölder factors of two irreducible
   representations to an actual equivalence, and from that equivalence to a
   categorical isomorphism of smooth representations. This step is generic
   and uses the published Jordan–Hölder comparison
   (`Filtration.JordanHolderComparisonProof`). That module does not itself
   prove Theorem 1.9.

None of these inputs is supplied by this proposition definition or its
citations. In this route, irreducibility and commutativity apply directly to
the supplied blocks, so no transport between socle representatives is
needed. A different route, for example a nonzero standard intertwining
operator, is acceptable once its construction and invertibility under these
hypotheses are proved.

## Dependency boundary and independence

The sole direct import is the unchanged
`Classification.SegmentProductPermutation`, which supplies the datum
permutation and imports `Classification.LanglandsData` and
`Group.GL.AdjacentMergeShape`. This statement neither imports nor applies
`AdjacentUnlinkedSegmentSwap`, the special-head adjacent swap, or
`TwoSegmentHeadCommutation`, the special-head two-factor interface.

This two-factor result is an input to the full-product lifting
`AdjacentUnlinkedSegmentSocleSwap` (task
`e3634665-571b-4852-9f4c-bab8a1053434`, proof successor
`cded83f3-df9c-4018-bc61-dc54f5c1f9ab`). It must not be derived by
specializing that proposition or any of its proof successors. The future
proof must also be independent, directly and transitively, of:

- `OrderedMultisegmentSocleExistence` and task
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`;
- independent socle exhaustion, task
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`;
- segment analytic classification, task
  `aca8805b-054f-4d56-8045-12db7f623404`;
- special-head multisegment exhaustion, task
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
- ordered special-head existence, task
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- tempered block uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c`;
- `SquareIntegrableLanglandsClassification` and task
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
- square-integrable exhaustion, task
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
- regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac`.

These exclusions cover mathematical conclusions, proof successors and
transitive proof dependencies. Shared lower results may be used only after
their proof dependencies are checked, and the proof Markdown must record that
audit. The future final theorem must have precisely this proposition as its
target, without extra theorem-valued assumptions. A proposition definition,
citation, conditional assembly or pending task is not a proved input.
