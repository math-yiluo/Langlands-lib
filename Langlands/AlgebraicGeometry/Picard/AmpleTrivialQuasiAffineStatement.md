# Quasi-affineness from an ample trivial line bundle

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
errata file was present in the Library's
`notes/errata/` when checked.

## Proof obligations and reuse

This module defines the statement and supplies no proof of it. The Library's
proof is `ampleTrivialQuasiAffine` (module
`Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineProof`). An elementary
route is to use the given isomorphism, the published tensor
bifunctor, and its unitors to construct an isomorphism from each actual
`tensorPow L.obj n` to the structure sheaf. Transport a global section
through that isomorphism to a global function. One must then prove that
its whole maximal trivialization open equals the basic open of that
function. Together with compactness and the affine generation opens from
ampleness, this would give the hypotheses of Mathlib's
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`.
The source uses a Proj argument; this route does not assert that any of its missing
comparisons have been proved.

The actual isomorphisms of the powers to the structure sheaf allow this
route to avoid general preservation of local rank one under tensor powers.
The published residue comparison
`Langlands.SchemeModule.lineBundleSectionResidueComparison` in
`Modules.SectionResidueComparison`, the existing tensor and pullback-tensor
work, and the monoidal work must be reused where needed. General preservation of
local rank one under tensor powers is the Library's `tensorPow_isLocallyFreeRankOne`.
Sheaf-isomorphism transport
of ampleness is the Library's `ampleIso` (module `Picard.AmpleIsoProof`).

A proof must prove this entire named proposition without added
hypotheses, in
Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The proper-scheme finiteness
criterion `ProperAmpleTrivialFiniteStatement` is a separate downstream target; its
proof `properAmpleTrivialFinite` uses `ampleTrivialQuasiAffine`.
