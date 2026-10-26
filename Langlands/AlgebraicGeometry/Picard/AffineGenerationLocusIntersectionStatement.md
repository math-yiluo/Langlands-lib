# Affineness of an affine open intersected with a line-bundle section locus

`Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionStatement`
is the universe-polymorphic proposition

```lean
∀ (X : Scheme.{u}) (L : LineBundle X)
  (s : Langlands.SchemeModule.GlobalSections L.obj) (U : X.Opens),
  IsAffineOpen U →
    IsAffineOpen (U ⊓ Langlands.SchemeModule.trivializationOpen L.obj s)
```

`LineBundle X` is the unchanged Library full subcategory of actual scheme-module
sheaves locally free of rank one. `GlobalSections L.obj` is the actual group
`Γ(L.obj, ⊤)`. The open `trivializationOpen L.obj s` is the supremum of all
opens on which restriction of the section morphism from the structure module
is an isomorphism. The infimum of opens is their intersection, and
`IsAffineOpen` means that the entire associated open subscheme is affine.

The sole premise after choosing `X`, `L`, `s`, and `U` is affineness of `U`.
There are no additional separation, noetherianity, quasi-compactness,
quasi-coherence, residue-comparison, tensor-coherence, or rank-one premises.
The rank-one property is already part of `L`. Arbitrary universes and schemes,
including empty and nonreduced schemes, are retained. The conclusion concerns
the whole intersection.

## Original source and correspondence

The registered original is
`stacks-ampleness-tensor-isomorphism-2026-10-24`, *Stacks Project — Ampleness
tensor and isomorphism transport (HTML snapshot 2026-10-24)*, retained at
`literature/Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)/01PR.html`.
Its directory SHA256 is
`23bfc9d1d2b4467556c7308dd203f22596c80d2f5276f1d5f9829673427e2f2d`.
The precise locator is [Lemma 28.27.4, tag 01PV](https://stacks.math.columbia.edu/tag/01PV),
together with the definition of `X_s` at the start of Section 28.27.
The retained lemma and its complete proof were read. No source-specific
`notes/errata/stacks-ampleness-tensor-isomorphism-2026-10-24.md` was present
in the workspace, project, or current Library when checked on 2026-10-26.

The source quantifies over a scheme, an invertible module, a global section,
and an affine open, and concludes that the intersection with `X_s` is affine.
Its proof explicitly uses the affine module description as locally free of
rank one, matching the Library's local definition of `LineBundle`.
The source defines `X_s` by nonvanishing in the residue-field fibre.
The Library theorem
`Langlands.SchemeModule.lineBundleResidueOpenComparison`, in
`Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`, already proves
for every such `X`, `L`, and `s` that

```text
nonvanishingLocus L.obj s = (trivializationOpen L.obj s : Set X).
```

Thus the Library's whole maximal trivialization open represents precisely the
source locus. This comparison is an available theorem to import in the proof
successor; it is not an extra premise of this statement.

## Separate proof obligation

This module defines a proposition and proves no affineness result. The source
reduces to an invertible module `N` on an affine scheme `Spec R`, forms
`B = Sym_R(N)/(s - 1)`, and identifies `Spec B` with the entire nonvanishing
open. A proof successor must establish this geometry or give another complete
argument for the actual Library locus. Affine neighborhoods alone do not give
the asserted conclusion, and arbitrary intersections of affine opens need not
be affine on an arbitrary scheme.

The successor must prove this entire named proposition without outer
hypotheses, in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
This focused statement is independent of the tensor-power, rank-one, pullback,
and ampleness-transport obligations owned by other tasks.
