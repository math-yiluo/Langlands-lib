# Quasi-affineness from an ample trivial line bundle

Author: Worker 665.

`Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineStatement.{u}`
is the proposition

```lean
∀ (X : AlgebraicGeometry.Scheme.{u})
  (L : Langlands.AlgebraicGeometry.Picard.LineBundle X),
  L.IsAmple →
    Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf) →
      AlgebraicGeometry.Scheme.IsQuasiAffine X
```

`LineBundle X` is the published full subcategory of actual module sheaves
locally free of rank one. `L.IsAmple` is the published predicate from
`Picard.Ample`: it asserts `CompactSpace X` and, through every point, an
affine whole maximal trivialization open of a global section of a positive
actual tensor power of `L.obj`. These powers use the sheafified tensor
bifunctor from `Modules.Tensor`, with zeroth power the structure sheaf and
successor power `tensorObj L.obj (tensorPow L.obj n)`.

The second hypothesis is existence of an actual isomorphism of module sheaves
with the structure sheaf. The conclusion is Mathlib's `Scheme.IsQuasiAffine`
from `Mathlib.AlgebraicGeometry.QuasiAffine`, which includes compactness and
the immersion property of the canonical map to the spectrum of global
functions; Mathlib also proves that this map is an open immersion.
All schemes in arbitrary universe `u` are quantified, including empty and
nonreduced schemes. There are no additional geometric or comparison
hypotheses. In particular, no field, properness, separatedness,
quasi-coherence, residue comparison, tensor-rank-one, monoidal coherence,
or basic-open condition is a premise.

## Source correspondence

The registered original is
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`,
*Stacks Project — Ample powers, closed restriction and quasi-affineness
(HTML snapshot 2026-10-24)*, retained file
`literature/Stacks Project - Ample powers, closed restriction and quasi-affineness (HTML snapshot 2026-10-24)/01QD.html`.
Its directory SHA256 is
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
The precise locator is Section 28.28, Lemma 28.28.1, tag
[01QE](https://stacks.math.columbia.edu/tag/01QE).

The source equates quasi-affineness of an arbitrary scheme with ampleness
of its structure sheaf. This statement takes the implication from ampleness
to quasi-affineness and formulates it invariantly under the displayed actual
sheaf isomorphism. The retained theorem, proof, and section comments were
read, and the live lemma was checked on 2026-10-26. The section comments
confirm that Stacks includes quasi-compactness in quasi-affineness, matching
Mathlib and the compactness already supplied by `L.IsAmple`. No source-specific
errata file was present in the workspace, current Library, or project
`notes/errata/` locations when checked.

## Remaining proof obligations and reuse

This module defines the statement and supplies no proof of it. An elementary
prospective route is to use the given isomorphism, the published tensor
bifunctor, and its unitors to construct an isomorphism from each actual
`tensorPow L.obj n` to the structure sheaf. Transport a global section
through that isomorphism to a global function. One must then prove that
its whole maximal trivialization open equals the basic open of that
function. Together with compactness and the affine generation opens from
ampleness, this would give the hypotheses of Mathlib's
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`.
The source uses a Proj argument; the prospective route does not assert
that any of its missing comparisons have already been proved.

The actual isomorphisms of the powers to the structure sheaf allow this
route to avoid general preservation of local rank one under tensor powers.
The published residue comparison
`Langlands.SchemeModule.lineBundleSectionResidueComparison` in
`Modules.SectionResidueComparison`, the existing tensor and pullback-tensor
work, and the monoidal work must be reused where needed. General tensor
rank-one work belongs to Worker 5, task
`242ed18d-863f-4b79-ab60-8cc71858988f`. Shared sheaf-isomorphism transport
of ampleness belongs to the positive-power workflow, Worker 410, task
`27374751-21ee-4c18-9874-c45f17b5eeb8`; coordinate with that owner if using
that route. Before substantial proof implementation, inspect the current
Library and owners and split any substantial missing geometric comparison
into a focused prerequisite.

The proof successor must prove this entire named proposition without added
hypotheses, in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The proper-scheme finiteness
criterion consumed by Worker 475 is a separate downstream target.
