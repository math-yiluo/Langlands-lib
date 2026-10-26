# Local linked-segment reduction for irreducible socle-product embeddings

Author: Worker 561.

`Langlands.Classification.LinkedSegmentSocleEmbeddingReduction.{uF,uV} F T`
is a proposition definition for the local reduction in Zelevinsky §6.7.
This module states the reduction and proves no representation-theoretic theorem.

For every prime `p`, p-adic field `F : PadicField.{uF} p`, and supplied compatible
topological data `T`, the definition installs exactly `T.topology`. The field
universe `uF` and carrier parameter `uV` are independent. It quantifies a rank
`n : ℕ`, actual data `d : T.SegmentProductDatum.{max uF uV,uF} n`, and an actual
smooth complex representation `π` of `GL_n(F)` in carrier universe
`max uF uV`. The hypotheses are precisely:

- `d.HasSegmentSocles`: every actual block is the irreducible socle of its
  segment's increasing cuspidal induction;
- `IsIrreducibleSubrepresentation d.induced.representation π.representation`:
  `π` is irreducible and an actual injective intertwiner embeds it into the
  full normalized product.

For each natural index `j` and witness `h : j+1 < d.length`, write
`Δ' = d.segments ⟨j, _⟩` and `Δ = d.segments ⟨j+1, h⟩`. If `Δ'.Precedes Δ`,
the conclusion is the following disjunction:

1. An actual injective intertwiner embeds `π` into the product of
   `d.permute (d.shape.adjacentSwap j h)`. This permutes the two actual blocks
   together with their segments and retains every other block.
2. There are an actual union segment `U`, an optional actual intersection
   segment `I`, and actual replacement product data `e` at the same rank `n`,
   satisfying all the support, list, socle, and embedding conditions below.

In the second branch, `U.support = Δ'.support ∪ Δ.support`. The match on `I`
has exactly two cases: `none` requires `Δ'.support ∩ Δ.support = ∅`;
`some J` requires `J.support = Δ'.support ∩ Δ.support`. Thus an empty
intersection is dropped. Every `Segment` already has positive length and
nonempty support, so it cannot encode an empty intersection. This includes
both overlapping and juxtaposed linked pairs.

The exact list equality is

```text
List.ofFn e.segments =
  (List.ofFn d.segments).take j ++ [U] ++ I.toList ++
    (List.ofFn d.segments).drop (j+2).
```

It preserves every outside segment occurrence in its original order, including
repetitions and their multiplicities. It requires more than equality of
multisets or of unions of supports. The existential `e` supplies actual
smooth blocks, a degree-sum witness at rank `n`, `e.HasSegmentSocles`, and
an actual irreducible embedding of `π` into `e.induced`. The list condition
does not identify the replacement datum's outside block representatives
with those of `d`; they must be actual socles of the retained segments.
No ordering condition is imposed on `e`.

The input uses the bare irreducible embedding relation. The stronger
`d.IsZelevinskySubrepresentation π` would also require precedence ordering
and would exclude precisely the adjacent inversion under consideration.
There is no total order, common chosen representative, finite-length,
filtration, classification, or theorem-valued premise. There are no internal
helper predicates hiding additional conditions. The imported definitions
use actual upper normalized induction with right translation.

## Source and derivation

The registered original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), 165–210, literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained PDF is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
The local disjunction is the step preceding Cases 1 and 2 of §6.7,
printed p.190 / one-based PDF p.27. Worker 561 read this page and
§§4.1–4.6, printed pp.184–186 / PDF pp.21–23, and visually checked
printed pp.185 and 190. No matching source errata entry was found in the
available project notes or literature index.

Proposition 4.6, printed pp.185–186 / PDF pp.22–23, assumes `Δ'` precedes
`Δ` and treats the reversed product `⟨Δ⟩ × ⟨Δ'⟩`. It gives a unique
irreducible submodule `K` and quotient
`⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`, with the empty intersection omitted. The latter
is irreducible by the sufficient direction of Theorem 4.2, proved before
Proposition 4.6. The present input instead has the forward pair
`⟨Δ'⟩ × ⟨Δ⟩`. Theorem 1.9, printed p.174 / PDF p.11, supplies equality
of composition factors of the two orders, not a canonical short exact
sequence for the forward pair. Exactness and associativity of normalized
induction are in Proposition 1.1(a),(c), printed p.170 / PDF p.7, with
tensor compatibility in Proposition 1.5, printed p.171 / PDF p.8.
Worker 561 read these passages as well.

The exact statement is a derived formulation of that source step in the
Library's actual-data language. Its proof must construct a finite filtration
of the forward pair with the two irreducible factors just described.
It must then induce that filtration through every fixed outside tensor
factor and normalized induction, and use actual regrouping equivalences
to identify the resulting full products. A Grothendieck equality alone
does not provide these maps or the required embeddings.

The elementary algebraic step has an independent justification: given a
finite filtration from zero to an ambient representation and an embedding
of a simple representation into it, take the first filtration term whose
preimage under the embedding is nonzero. Simplicity makes that preimage
the whole source. The preimage of the preceding term is zero, so projection
to the corresponding successive quotient remains injective. After the
graded-quotient equivalence, this is an embedding into one layer. A layer
containing `K` embeds into the swapped product by the reverse-pair
embedding and exactness; the other layer is the union/intersection
replacement. These are proof obligations, not results implemented here.

## Independence and remaining inputs

The two imports provide the published segment-product permutation and actual
constituent relations; neither is a premise asserting this reduction.
This statement assumes no exhaustion or analytic classification result.
An exact proof must independently establish the two-factor filtration,
the generic finite-filtration and induction steps, replacement data with
degree preservation, and actual transport. Existing owners must be reused
where their precise targets apply.

The proof must exclude, directly and transitively, the conclusions of
socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, analytic segment
classification `aca8805b-054f-4d56-8045-12db7f623404`, special-head
exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head
existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`,
`SquareIntegrableLanglandsClassification` and task
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`. Proof successors of those
conclusions are also excluded. Independently justified lower inputs may
be reused after a dependency audit. No proposition definition, citation,
conditional assembly lemma, or pending task counts as a proved input.
