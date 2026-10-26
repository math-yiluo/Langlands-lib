# Gluing of the forward product of two linked segment socles

Author: Worker 238. The interface was agreed with Worker 494, who needs it as
the two-factor input of the full-product reduction
`LinkedSegmentSocleEmbeddingReduction` (task
`0f459af5-e039-4eee-a8bd-9d8d2f508936`) inside independent socle exhaustion
(task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`).

`Langlands.Classification.LinkedSegmentSocleGluing.{uF,uV} F T` is a
Prop-valued definition, not a proof. For two segments whose first precedes the
second, it asks for an actual two-step filtration of the forward induced
product of their supplied segment socles. One graded piece is isomorphic to a
product of segment socles for the union and the nonempty intersection; the
other admits an injective equivariant map into the reverse product.

## Exact proposition

Fix any `p : ℕ` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The declaration installs `T.topology`.
The field universe `uF` and carrier parameter `uV` are independent. Writing
`v = max uF uV`, all segments and data use `T.Segment.{v,uF}` and
`T.SegmentProductDatum.{v,uF}`.

For every `n : ℕ`, every `d : T.SegmentProductDatum.{v,uF} n`, and every
`h₂ : d.length = 2`, write `Δ' = d.segments ⟨0, _⟩` and
`Δ = d.segments ⟨1, _⟩` (the bounds come from `h₂`). Assume

- `d.HasSegmentSocles`, that is, every supplied block `d.blocks i` satisfies
  `T.IsSegmentSocle (d.segments i) (d.blocks i)`;
- `Δ'.Precedes Δ`.

Let `σ = d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)`. The
conclusion asserts the existence of `U : T.Segment.{v,uF}`,
`I : Option (T.Segment.{v,uF})` and `e : T.SegmentProductDatum.{v,uF} n` with

1. `Δ'.IsUnionIntersectionReplacement Δ U I`, that is,
   `U.support = Δ'.support ∪ Δ.support`, and either `I = none` and
   `Δ'.support ∩ Δ.support = ∅`, or `I = some J` and
   `J.support = Δ'.support ∩ Δ.support`;
2. `List.ofFn e.segments = U :: I.toList`, so `e` lists the union segment
   followed by the intersection segment when it is nonempty, and has length
   one or two accordingly;
3. `e.HasSegmentSocles`;
4. there are `s : ObjectRepFiltration (Rep.of d.induced.representation) 2`
   and `i j : Fin 2` with `i ≠ j`,

   ```text
   Nonempty ((s.gradedRepresentation i).ρ.Equiv e.induced.representation)
   ```

   and an intertwining map

   ```text
   f : (s.gradedRepresentation j).ρ.IntertwiningMap
         (d.permute σ).induced.representation
   ```

   with `Function.Injective f`.

`ObjectRepFiltration A 2` is the published chain
`0 = S₀ ≤ S₁ ≤ S₂ = A` of invariant subspaces of the actual representation
`A`, and `s.gradedRepresentation k` is the actual quotient `S_{k+1}/S_k`.
`Representation.Equiv` is an invertible equivariant complex-linear map and
`Representation.IntertwiningMap` an equivariant complex-linear map.

`d.induced` is the forward product `⟨Δ'⟩ × ⟨Δ⟩` of the supplied blocks.
`d.permute σ` sends new position `k` to original label `σ k`, retaining each
supplied block with its segment, so `(d.permute σ).induced` is the reverse
product `⟨Δ⟩ × ⟨Δ'⟩` of the same supplied blocks. The replacement datum `e`
is existential and includes its own actual blocks, which must be segment
socles, and its own degree-sum witness at the same rank `n`.

The orientation is not prescribed: either the union/intersection piece is the
subrepresentation `S₁` and the other piece is the quotient, or conversely.
There is no order, finite-length, irreducibility, genericity or supplied
gluing premise. Every natural rank is quantified; rank zero is vacuous since
each segment has positive degree. Both overlapping and juxtaposed linked pairs
are included; for a juxtaposed pair the intersection is dropped rather than
encoded as a zero-length segment.

## Conventions

The unchanged imported definitions use normalized induction from the standard
upper block parabolic, positive half-modulus covariance and right translation.
For `Δ = [ρ, νρ, …, ν^(m-1)ρ]`, with `ν = |det|_F` and `|ϖ|_F = q^(-1)`,
`Precedes Δ' Δ` means that the two segments are linked and the base of `Δ` is
the twist of the base of `Δ'` by a positive integral power of `ν`.
`IsSegmentSocle` makes a block the irreducible subrepresentation of the
increasing cuspidal induction, including uniqueness of its image among
irreducible subrepresentations; it does not assert that socles have been
constructed for every segment.

## Derived provenance

This is a derived two-factor interface for the gluing step in A. V.
Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Registered source: `zelevinsky-1980-induced-ii`; SHA256:
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

- §4.1, printed p.184 (one-based PDF p.21), defines linked, juxtaposed and
  precedence for segments.
- Proposition 4.6, printed pp.185–186 (PDF pp.22–23): with
  `Δ∪ = Δ ∪ Δ'`, `Δ∩ = Δ ∩ Δ'` (omitted if empty) and
  `ω = ⟨Δ∪⟩ × ⟨Δ∩⟩`, if `Δ'` precedes `Δ` then `π = ⟨Δ⟩ × ⟨Δ'⟩` has a
  unique irreducible submodule `ω₀`, `ω₀ ≇ ω`, and `π/ω₀ ≅ ω`. The
  irreducibility of `ω` is the implication (2)⇒(1) of Theorem 4.2, printed
  p.184 (PDF p.21).
- Theorem 1.9, printed p.174 (PDF p.11): `π₁ × π₂` and `π₂ × π₁` have the
  same composition factors.
- Theorem 6.1(a), printed p.188 (PDF p.25): `⟨Δ, Δ'⟩` is the unique
  irreducible submodule of `⟨Δ⟩ × ⟨Δ'⟩`.
- §6.7, printed p.190 (PDF p.27): "By 4.6, 1.9 and 6.1(a) `⟨Δ'⟩ × ⟨Δ⟩` is
  glued together from `⟨Δ, Δ'⟩` and `⟨Δ∪, Δ∩⟩ = ⟨Δ∪⟩ × ⟨Δ∩⟩`", followed by
  the case analysis that embeds an irreducible subrepresentation in one of the
  two pieces.

The Lean proposition is the actual-filtration form of that gluing sentence for
the forward pair, `Δ'` first. It is deliberately weaker than the source in two
respects, which are all that §6.7 uses: the second piece is only required to
embed into the reverse product, rather than being identified with
`⟨Δ, Δ'⟩` and shown irreducible, and the orientation of the two pieces is
not fixed. It does not assert that `e.induced` is irreducible, and it asserts
no canonical short exact sequence for the forward pair. The Lean `e` uses
existentially chosen socle blocks for `Δ∪` and `Δ∩`, matching the source's
`⟨Δ∪⟩` and `⟨Δ∩⟩` up to isomorphism.

The original pages listed above and the published
`notes/henniart/gln-classification-sources.md` were read. No source-specific
errata note for `zelevinsky-1980-induced-ii` was present in the supplied
public notes.

## Proof obligation and independence

A future proof must construct the actual filtration and maps for the supplied
blocks. A Grothendieck-group identity alone does not supply the filtration:
an actual two-step filtration of the forward product, an isomorphism of one
layer with the chosen union/intersection product and an embedding of the other
layer into the reverse product are all required. Segment socle existence for
`Δ∪` and `Δ∩`, Proposition 4.6 for the reverse product, constituent
commutativity (Theorem 1.9, whose source proof uses the Gelfand–Kazhdan
involution) and a length-two layer-matching argument are separate obligations,
not supplied by this proposition definition or its citations.

The statement imports only the published `SegmentProductPermutation`,
`SegmentReplacementInversions` and `Filtration.ObjectDefinitions` pairs, all
unchanged. Its future proof must preserve direct and transitive independence
from:

- independent socle exhaustion, task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`,
  and the linked full-product reduction, task
  `0f459af5-e039-4eee-a8bd-9d8d2f508936`, which consume this statement;
- segment analytic classification, task
  `aca8805b-054f-4d56-8045-12db7f623404`;
- multisegment special-head exhaustion, task
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
- ordered special-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- tempered block uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c`;
- `SquareIntegrableLanglandsClassification` and task
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
- square-integrable exhaustion, task `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
- regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac`.

The exclusions cover mathematical conclusions, proof successors and transitive
proof dependencies. Shared lower results require an independence audit before
reuse. The future exact proof must have precisely this proposition as its
target, without extra theorem-valued assumptions. Statements, citations,
drafts and pending tasks are not proof evidence.
