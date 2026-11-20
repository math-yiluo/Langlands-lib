# Frame charts from the frame-normalized Hilbert locus

This module proves a reduction of the published `FrameChartRepresentabilityStatement` to six
named statements. It proves none of the six. All schemes lie in universe `0`.

## Main declaration

`frameChartRepresentability_of_frameHilbertLocus` is a proved definition (a term of
`FrameChartRepresentabilityStatement`) taking as arguments:

1. `HL : FrameHilbertLocusStatement` — the frame-normalized relative form of GIT
   Proposition 7.3 (module `FrameHilbertLocusStatement`);
2. `HP : CubicBundlePolarizationDeterminationStatement.{0}` — the polarization is determined
   by the cubic bundle up to a twist from the base;
3. `Hbc : FrameLocusBaseChangeStatement.{0}` — the published base-change statement of the
   frame locus;
4. `Hiso : FrameLocusIsoInvarianceStatement.{0}` — the frame locus depends only on the
   isomorphism class of a datum;
5. `HE : FrameEmbeddingExistenceStatement.{0}` — every datum with frame locus `⊤` over a
   locally noetherian base has a frame-normalized cubic embedding (its proof uses Lefschetz,
   `CubicFieldEmbeddingStatement`);
6. `HU : FrameEmbeddingUniquenessStatement.{0}` — such an embedding is unique.

## Implemented proof

Fix `P g d n hd hn ρ` and `m = cubicProjectiveDimension g d`.

- `exists_relativeProjectiveFamily_classifying` (module `HilbertClassifying`) gives a locally
  noetherian `S` with a flat, finitely presented family `(IS, σS)` in `ℙ^m_S` indexed by the
  level coefficient tuples, classifying such families on every scheme. (`NeZero n` follows
  from `3 ≤ n`, so the tuples form a finite type.)
- `HL` applied to `(S, IS, σS)` gives an immersion `j : S' ⟶ S` from a level base, a datum
  `U` over `S'` with frame locus `⊤`, a frame-normalized embedding of `U` realizing
  `j^*(IS, σS)`, and the factorization property.
- `exists_isUniversalFrameDatum` shows `U` is a universal frame datum
  (`IsUniversalFrameDatum`, module `FrameChartUniversalDatum`):
  * injectivity: if `U.pullback f ≅ U.pullback f'`, base change of `U`'s embedding
    (`Datum.IsFrameEmbedding.pullback`, `Datum.Realizes.pullback`) gives frame-normalized
    embeddings realizing `(f ≫ j)^*` and `(f' ≫ j)^*` of the family; both pullbacks have
    frame locus `⊤` by `Hbc`; transport along the isomorphism
    (`IsFrameEmbedding.ofPolarizedIso`) and `HU` give equal families
    (`Datum.Realizes.eq_of_polarizedIso`), so `f ≫ j = f' ≫ j` by uniqueness of classifying
    maps, and `f = f'` since immersions are monomorphisms;
  * every datum `b` with frame locus `⊤` is a pullback: `HE` gives an embedding, whose family
    is flat (`IsFrameEmbedding.flat`) and so classified by some `t : T ⟶ S`; `HL` factors
    `t = t' ≫ j`; the pullback of `U` along `t'` realizes the same family, and
    `Datum.nonempty_polarizedIso_of_realizes` (with `HP`) gives `b ≅ U.pullback t'`;
  * data isomorphic to pullbacks of `U` have frame locus `⊤` by `Hiso` and `Hbc`.
- `frameChart_of_isUniversalFrameDatum` turns the universal frame datum into the natural
  transformation required by the target.

`Datum.Realizes.eq_of_polarizedIso` is the auxiliary lemma: isomorphic data, the first with
frame locus `⊤`, realize the same family by any of their frame-normalized embeddings (from
`HU` and transport).

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## What is not proved

The six arguments above. `HL` is the deep geometric input (GIT steps I–VI: smooth and
connected locus, Theorem 6.14, torsion and level loci, Proposition 6.11, rigidification
locus). `HE` needs the Lefschetz statement `CubicFieldEmbeddingStatement` (Task 7747).

## Provenance

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), §7.2, printed
pp.131–134 (PDF pp.144–147), registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`: the injection
of the functor of rigidified data into the Hilbert scheme with sections, and Proposition 7.3
(its image is a locally closed subscheme), in the frame-normalized form described in
`FrameChartRepresentabilityStatement.md`.
