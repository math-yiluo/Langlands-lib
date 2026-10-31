# Dimension of a quasi-compact smooth scheme over a field

`Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement.{u}` is the
following `Prop`-valued definition:

```lean
∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ),
  SmoothOfRelativeDimension g f → CompactSpace X →
    topologicalKrullDim X ≤ (g : WithBot ℕ∞)
```

In words: let `k` be a field and `X` a scheme with a morphism `f` from `X` to
`Spec k`, both in the arbitrary universe `u`. If `f` is smooth of relative
dimension `g` and `X` is quasi-compact, then the underlying topological space
of `X` has Krull dimension at most `g`.

## The hypotheses and the conclusion

- `k` is an arbitrary field. It need not be algebraically closed or perfect,
  and its characteristic is arbitrary.
- `f : X ⟶ Spec (CommRingCat.of k)` is an arbitrary morphism, that is, a
  `k`-scheme structure on `X`.
- `SmoothOfRelativeDimension g f` is Mathlib's
  `AlgebraicGeometry.SmoothOfRelativeDimension` (in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`), as an explicit hypothesis.
  Every point of `X` lies in an affine open whose ring of sections is standard
  smooth of relative dimension `g` over the sections of an affine open of the
  base.
- `CompactSpace X` says that the underlying space of `X` is compact, that is,
  that `X` is quasi-compact. There is no connectedness, irreducibility,
  properness or separatedness hypothesis. `X` may be empty, in which case its
  dimension is `⊥`.
- `topologicalKrullDim X` is Mathlib's `topologicalKrullDim` (in
  `Mathlib.Topology.KrullDimension`): the Krull dimension of the poset of
  irreducible closed subsets of the underlying space, that is, the supremum of
  the lengths of chains of irreducible closed subsets, valued in
  `WithBot ℕ∞`. The conclusion bounds it by the natural number `g` cast into
  `WithBot ℕ∞`. So the dimension is finite.

The conclusion is an inequality only. Its intended use is a cohomological
vanishing bound above the dimension. No dimension carrier is supplied: the
dimension being bounded is that of the actual underlying topological space.

This file defines the proposition only. It provides no proof. A separate proof
task is to prove this exact published proposition.

## Derived provenance

This is an internal derived statement. It combines the published Library
statement on stalk dimensions at closed points with the description of the
dimension of a space through chains of irreducible closed subsets. No single
source states this Lean interface.

1. The published proposition
   `Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement`
   (module of the same name) states that under `SmoothOfRelativeDimension g f`
   the stalk `𝒪_{X,x}` has Krull dimension exactly `g` at every closed point
   `x` of `X`. This declaration is itself a statement target, not a theorem.
   Its Markdown derives the target from Stacks Tag 02G1 (Lemma 29.35.12)
   and Tag 0A21, item (2) (Lemma 33.20.3), with the full source records.
   Tag 02G1 identifies the rank of the relative differentials with the
   local dimension of the fibre, and item (2) identifies local topological
   dimension with stalk dimension at a closed point. The retained source
   for 02G1 is `stacks-smooth-differential-rank-2026-10-22`, folder
   `literature/Stacks Project - Smooth morphisms and differential rank (HTML snapshot 2026-10-22)`
   (source-folder SHA-256
   `a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`),
   file `01V4.html` (SHA-256
   `4327b0dc32a5b7a4fc554e6587f0d622d978e306bba4d2783a8aade3704aa3da`),
   Lemma 29.35.12 and adjoining Definition 29.35.13 (Tag 02G2).

2. **Tag 0A21, item (5)** (Lemma 33.20.3). Source ID
   `stacks-flasque-affine-vanishing-kunneth-a04446e5`, folder
   `literature/Stacks Project - Flasque sheaves, affine vanishing and Kunneth over a field (source at a04446e5)`
   (source-folder SHA-256
   `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`), file
   `varieties.tex` (SHA-256
   `53d0af48818d22ae85675eff76b79fcad4335fda0b4574ec09f5c9e73cc93995`),
   `lemma-dimension-locally-algebraic`, item
   `item-dimension-irreducibles-passing-through`, at line 3804, with its proof
   from line 3894; `tags.txt` line 12689 maps the lemma to 0A21,
   [Stacks Tag 0A21](https://stacks.math.columbia.edu/tag/0A21).
   For a locally algebraic `k`-scheme, item (5) identifies `dim_x(X)` with
   both the largest dimension of an irreducible component containing `x`
   and the smallest stalk dimension at a closed specialization of `x`.
   Its proof passes to an affine neighbourhood and invokes the
   corresponding finite-type algebra result. Item (2) is at lines
   3789-3792, with proof at lines 3867-3870. The published stalk-statement
   Markdown records that the two web comments on 0A21 correct item (9)(d);
   they do not concern items (2) or (5). No separate errata note for either
   retained source was found.

The mathematical derivation of the proposed bound is as follows; it is not
implemented as a Lean proof in this file. A smooth morphism is locally of
finite presentation (Stacks Tag 01VE, Lemma 29.35.8, in the retained
`01V4.html`), hence locally of finite type, so `X` is a locally algebraic
`k`-scheme. Let `Z₀ ⊊ Z₁ ⊊ ⋯ ⊊ Zₘ` be a chain of irreducible closed subsets
of `X`. Every nonempty closed subset of a quasi-compact scheme contains a
point closed in the whole scheme: its underlying space is compact and T₀,
so `IsClosed.exists_closed_singleton` applies. Choose such a point `x` in
`Z₀`. The generic points of the `Zᵢ` form a chain of specializations which
can be extended to end at `x`. An affine neighbourhood of `x` contains all
these generic points. In its coordinate ring, their distinct prime ideals
are contained in the prime of `x`, and remain a strict chain of length `m`
after localization at that prime. This is a chain in `𝒪_{X,x}`. The
closed-point stalk dimension equality targeted by item 1 therefore gives
`m ≤ dim(𝒪_{X,x}) = g`. Taking the supremum of these chain lengths yields
the proposed topological Krull dimension bound.

Item (5) of 0A21 expresses the same relation in terms of local topological
dimension: every point has a closed specialization, all the closed
specializations have stalk dimension `g` by the stalk target, and the
minimum in that item is therefore `g`. In Mathlib the comparison of the
stalk dimension with chains of specializations is
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`. Neither this comparison
nor the stalk statement is an import dependency of the present definition.

The quasi-compactness hypothesis is a restriction made for the proof: it gives
closed points in every nonempty closed subset without a Jacobson argument. The
intended application, an abelian variety over a field, is proper and hence
quasi-compact.

## Imports

The module imports only Mathlib: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
for `AlgebraicGeometry.SmoothOfRelativeDimension` and
`Mathlib.Topology.KrullDimension` for `topologicalKrullDim`.
