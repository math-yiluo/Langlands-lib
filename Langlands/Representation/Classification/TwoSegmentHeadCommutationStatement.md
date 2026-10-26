# Commutation of two unlinked special segment heads

Author: Worker 485. The exact interface and independence requirements were
supplied through coordination by Worker 422 and Worker 17.

`Langlands.Classification.TwoSegmentHeadCommutation.{uF,uV} F T` is a
Prop-valued definition, not a proof. It asks for an actual categorical
isomorphism between the normalized induced products of two supplied special
segment heads in the two orders.

## Exact proposition

Fix any `p : ℕ` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The declaration installs `T.topology`.
The field universe `uF` and carrier parameter `uV` are independent. Writing
`v = max uF uV`, the segments and actual smooth complex representation blocks
in the datum use the specified `T.SegmentProductDatum.{v,uF}` universe.

For every `n : ℕ`, every `d : T.SegmentProductDatum.{v,uF} n`, and every
`h₂ : d.length = 2`, assume `d.HasSegmentHeads` and

```text
¬ (d.segments ⟨0, by omega⟩).IsLinked (d.segments ⟨1, by omega⟩).
```

The two indices and the bound for the adjacent swap are justified using
`h₂`. Let `σ = d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)`.
The conclusion is exactly

```text
Nonempty (d.induced ≅ (d.permute σ).induced).
```

The isomorphism is in the actual smooth complex representation category of
`GL_n(F)` and consists of invertible equivariant complex-linear maps. By the
published `SegmentProductDatum.permute_induced`, its right side is also

```text
(T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
  (fun i => d.blocks (σ i)).
```

The permutation sends new position `i` to original label `σ i`.
`SegmentProductDatum.permute` definitionally retains each supplied block,
with its corresponding segment and degree. It does not choose replacement
representatives or discard occurrences. Repeated or equal segments are
allowed; a segment is not linked to itself under the existing definition.

There is no order, genericity, unitarity, whole-product irreducibility,
finite-length, or supplied commutation premise. Every natural ambient rank
is quantified. Rank zero is vacuous here: the datum has two segments, each
has positive degree, and their degree sum equals the ambient rank. This
statement concerns exactly two factors; swapping adjacent factors inside a
larger product requires a separate lifting argument.

## Conventions and derived provenance

The unchanged imported definitions use normalized induction from the standard
upper block parabolic, positive half-modulus covariance and right translation.
For `Δ = [ρ, νρ, …, ν^(m-1)ρ]`, with `ν = |det|_F` and
`|varpi|_F = q^(-1)`, a supplied `IsSegmentHead` witness makes the block the
irreducible head of the increasing cuspidal induction. The relation includes
uniqueness of the kernels of its irreducible quotient maps. It selects the
special quotient, distinct from the segment socle; it does not assert that
such a head has been constructed for every segment.

This interface is a derived two-factor actual-isomorphism consequence of the
unlinked special-head product theory in A. V. Zelevinsky, *Induced
representations of reductive p-adic groups II. On irreducible representations
of GL(n)*, Ann. Sci. ENS (4) 13 (1980), pp.165–210. Registered source:
`zelevinsky-1980-induced-ii`; SHA256:
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

Section 9.1, printed p.197 (one-based PDF p.34), fixes the increasing-product
special quotient convention. Theorem 9.7(a),(b), printed p.199 (PDF p.36),
and its argument in §§9.8–9.10, printed pp.199–201 (PDF pp.36–38), give the
unlinked special-head product setting. In particular §9.10 identifies an
unlinked product with an irreducible isomorphism class determined by the
multiset. Reversing two unlinked factors preserves that multiset. This is
the provenance rationale for the two-factor interface, not an invocation of
an already proved Library classification theorem or a literal transcription
of a full-product categorical lifting theorem.

Those original pages and the published
`notes/henniart/gln-classification-sources.md` were read. No source-specific
`notes/errata/zelevinsky-1980-induced-ii.md` was present in the supplied public
notes. The published source corrections are respected: §9.3 omits the
square-integrability converse proof, and the Auel/Jacquet discussion does not
supply a tempered exhaustion proof. Neither assertion is used here as a
proved input.

## Proof obligation and independence

A future proof must construct an actual isomorphism for the supplied blocks.
Grothendieck-group equality or matching Jordan–Hölder constituents alone does
not suffice. Independently proved irreducibility together with an appropriate
independently proved constituent comparison may supply a route. A suitable
nonzero standard intertwining operator may supply another route, once its
construction and invertibility under these hypotheses are proved. None of
these inputs is supplied by this proposition definition or its citations.

The existing `IsSegmentHead.nonempty_iso_segmentHead` in
`Classification.LanglandsQuotients` compares a supplied head to a chosen head
using that witness; it does not supply unconditional head existence.
`SegmentHeadProductIrreducibility` and the corresponding pending proof owner
are separate obligations, not proved assumptions of this statement. Reuse
existing lower owners before creating further prerequisite tasks.

The statement imports only `Classification.SegmentProductPermutation` and
the existing `Classification.Segments`; their pairs are unchanged. Its future
proof must preserve direct and transitive independence from:

- `GenericSegmentProductUniqueness`, task
  `30341ae4-65f2-4a0e-9283-763db01a409e`, and its conclusion;
- full-product adjacent lifting, task
  `8b684d6f-a2ce-4fe2-862d-0bd80597fd92`, and its proof successors;
- multisegment exhaustion, task `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
- ordered strong-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- ordered conversion, task `8252833d-c269-41a9-824c-5879e531b23b`;
- tempered uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c`;
- `SquareIntegrableLanglandsClassification` and task
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
- square-integrable exhaustion, task
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
- regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac`.

Shared lower results require an independence audit before reuse. In particular,
using the parent uniqueness result to prove this two-factor input would be
circular because the full-product lifting is intended to consume it. The
future final theorem must have precisely this proposition as its target,
without extra theorem-valued assumptions. Statements, citations, drafts and
pending tasks are not proof evidence.
