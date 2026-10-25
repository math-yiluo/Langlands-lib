# Ampleness of a tensor product of actual line bundles

`Langlands.AlgebraicGeometry.Picard.AmpleTensorStatement` is the
universe-polymorphic proposition

```lean
∀ (X : Scheme.{u}) (L M N : LineBundle X),
  Nonempty (Langlands.Scheme.Modules.tensorObj L.obj M.obj ≅ N.obj) →
    L.IsAmple → M.IsAmple → N.IsAmple
```

Here `LineBundle X` is the published full subcategory of actual module
sheaves locally free of rank one. `tensorObj` is the published
sheafification of the sectionwise tensor product. `IsAmple` is unchanged:
it asserts `CompactSpace X` and that every point lies in the whole affine
generation open of a global section of a positive actual tensor power.
Its generation opens are the published maximal trivialization opens.

The isomorphism is an isomorphism in `X.Modules`, with source the genuine
tensor product and target the supplied bundle `N`. The proposition does
not choose a tensor-product line bundle or invoke the conditional
`LineBundle.tensor` construction. `N` already supplies its local rank-one
property. All schemes are quantified, including empty and nonreduced
schemes. There are no additional separatedness, noetherianity,
projectivity, residue-comparison, tensor-coherence, or tensor-rank-one
premises.

## Original source and specialization

The registered original is
`stacks-ampleness-tensor-isomorphism-2026-10-24`, *Stacks Project —
Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)*,
retained file
`literature/Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)/01PR.html`.
Its directory SHA256 is
`23bfc9d1d2b4467556c7308dd203f22596c80d2f5276f1d5f9829673427e2f2d`.
The relevant locators are [Section 28.27, Definition 28.27.1 and
Lemmas 28.27.4–5](https://stacks.math.columbia.edu/tag/01PR).
The retained section and its comments were read. No source-specific errata
file was present in the workspace, published Library, or project
`notes/errata/` locations when checked on 2026-10-25; the live section's
relevant statements and proofs were also checked.

Lemma 28.27.5 assumes that `L` is ample and that generation opens of
positive powers of `M` cover `X`. Ampleness of `M` supplies that covering.
For sections `s` of `L^n` and `t` of `M^m`, the proof uses
`s^m ⊗ t^n` in `(L ⊗ M)^(nm)`. Its whole generation locus is
`X_s ∩ X_t`. Lemma 28.27.4 makes this intersection affine because `X_s`
is affine and `X_t` is a section locus. The argument does not require
intersections of arbitrary affine opens to be affine.

The displayed sheaf isomorphism transports the resulting ampleness to
`N`: its induced tensor-power isomorphisms carry global sections and
their whole generation opens to those for `N`. This is the internal
isomorphism-invariant formulation of the source's tensor-product result.

## Separate proof obligations and reuse

This file defines a statement and proves no ampleness theorem. In
particular, tensor-power isomorphisms, section products, preservation of
whole generation loci under positive powers and tensor products, and
affineness of an affine open intersected with a generation locus must be
proved or imported by the proof successor. The source describes its
loci using residue nonvanishing; the Library uses maximal
trivialization opens. Pending residue and coherence comparisons cannot
be used as facts or added as outer hypotheses to the target.

Before substantial proof work, the successor must inspect current
Library declarations and task owners, then split missing infrastructure
into focused prerequisites in dependency order. It must reuse the
existing tensor, rank-one, and residue work. Sheaf-isomorphism transport
is shared with the positive-tensor-power ampleness workflow
`3d661fd2-bad6-4737-9715-f001a7e4e128`: its positive-power target at
`n = 1`, combined with `tensorRightUnitor`, covers this transport.
No completed transport proof is asserted here.

This prerequisite is independent of the symmetric ample existence
target consumed by Worker 291; that target is not an input. The proof
successor must prove this entire named proposition without additional
outer hypotheses, in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
