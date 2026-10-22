# Relative global functions for smooth proper morphisms

Authors: Worker 124 and Worker 143. Worker 143 proposed the formulation and
identified the main source; Worker 124 checked the sources and Mathlib interface
and implemented this pair.

`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions.{u}` is a
proposition definition. It states that for every pair of schemes `X` and `S` in
the arbitrary universe `u`, and every morphism `p : X ⟶ S`, smoothness,
properness, and geometric connectedness of `p` imply
`∀ U : S.Opens, CategoryTheory.IsIso (p.app U)`.
The three hypotheses are explicit implications, and the schemes, morphism,
and every open subset of the base are quantified inside the proposition.

The canonical map is Mathlib's `AlgebraicGeometry.Scheme.Hom.app`:

```text
p.app U : Γ(S, U) ⟶ Γ(X, p ⁻¹ᵁ U)
```

This is a morphism in `CommRingCat`, defined as `p.c.app (op U)` in
`Mathlib/AlgebraicGeometry/Scheme.lean`. Thus the assertion concerns the
structure morphism's own pullback map on functions. It includes non-affine
opens and the empty open. `IsIso` requires that this particular map have an
inverse; an abstract isomorphism between the two section rings would not
suffice.

All geometry uses existing Mathlib definitions.
`AlgebraicGeometry.GeometricallyConnected p` requires connected pullbacks
along maps from spectra of fields; Mathlib's
`GeometricallyConnected.iff_geometricallyConnected_fiber` identifies this with
geometric connectedness of the fibres. Its use of `ConnectedSpace` includes
nonemptiness. No hypothesis is imposed that the base be connected,
noetherian, reduced, affine, or the spectrum of a field. There is no
projectivity, group structure, or characteristic restriction.

## Provenance and specialization

The main source is the Stacks Project, Lemma 36.32.6, Tag
[0E0L](https://stacks.math.columbia.edu/tag/0E0L). It treats proper, flat,
finitely presented morphisms whose geometric fibres are reduced and
connected, and identifies the pushforward of the structure sheaf with the
base structure sheaf, universally after base change.

The present statement is a derived specialization, for the following reasons.
Smoothness implies flatness and local finite presentation, as in Stacks
Section 29.35, Lemmas 29.35.8 and 29.35.9. Its stability under base change
(Lemma 29.35.5), together with Lemma 33.25.4 in Section 33.25, shows that the
fibres are geometrically reduced. Properness supplies quasi-compactness and
separatedness, hence quasi-separatedness; combined with local finite
presentation this is finite presentation in the sense of Definition
29.22.1. The relevant properness definition and quasi-compactness result are
Definition 29.42.1 and Lemma 29.42.8.

Evaluating the source's canonical structure-sheaf isomorphism on any open
`U` gives exactly `IsIso (p.app U)`. The declaration records this conclusion
for every smooth proper geometrically connected morphism over every base.
It does not separately encode a chosen base-change diagram or coherence
data; application to a base-changed morphism uses the same quantified
statement and stability of the hypotheses.

The pinned Mathlib supplies smooth-implies-flat and
smooth-implies-locally-of-finite-presentation instances in
`Morphisms/Smooth.lean`, and uses local finite presentation,
quasi-compactness, and quasi-separatedness as the finite-presentation
convention. These observations check the interface and source
correspondence; this module contains no proof of the global-functions
assertion or of its specialization from the source. A separate exact-target
proof obligation remains.

## Retained sources

- `stacks-relative-global-functions-0e0l-2026-10-22`, registered directory
  SHA256 `4f31e85523053c46b315dc46c77b611347154add7f98d9d89a57a748f3e85b87`,
  file `0E0L.html`, Lemma 36.32.6 and its proof. The proof's references to
  Lemma 36.32.5 and Varieties Lemma 33.9.3 are leads for the later proof;
  they are not assumed Lean results here.
- `stacks-smooth-differential-rank-2026-10-22`, registered directory SHA256
  `a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`,
  file `01V4.html`, Section 29.35, Lemmas 29.35.5, 29.35.8, and 29.35.9.
- `stacks-smooth-proper-specialization-2026-10-22`, registered directory
  SHA256 `8b7af7d4ca1a694f73056deb66f42883653c84de94821b7bce211337a2f0600a`:
  file `04QM.html`, Lemma 33.25.4 and its proof; file `01TO.html`,
  Definition 29.22.1; file `01W0.html`, Definition 29.42.1, Lemma 29.42.8,
  and the comments about finite presentation.

No source-specific project errata note was present when this statement was
prepared. The retained Tag 0E0L and Section 33.25 pages contain no comments.
The properness section's comment pointing out that properness alone need
not imply finite presentation is consistent with the explicit use of
smoothness above.
