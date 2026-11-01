# Embedding a line bundle as an invertible ideal on a quasi-affine scheme

`Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleIdealEmbeddingStatement.{u}`
states that every actual Library line bundle `D` on a locally Noetherian
quasi-affine scheme `X` has a monomorphism of actual module sheaves

```text
s : D.obj ⟶ SheafOfModules.unit X.ringCatSheaf.
```

Mathlib's `Scheme.IsQuasiAffine X` includes quasi-compactness. Together with
local Noetherianity this gives the Noetherian hypothesis in the source.
No reducedness, integrality, connectedness or factoriality is assumed.
The assertion includes empty schemes. It specifies an existential embedding,
without claiming a canonical choice.

The image of this monomorphism is an invertible ideal subsheaf of the
structure sheaf: it is isomorphic to the locally free rank-one source.
Locally, after a rank-one trivialization, the monomorphism is multiplication
by a non-zero-divisor. Thus this is the ideal-sheaf presentation of an
effective Cartier divisor. The statement uses the actual sheaf map directly;
it introduces no formal divisor group or substitute for a module sheaf.

The source is Stacks Project Lemma 31.16.12, Tag
[0AYM](https://stacks.math.columbia.edu/tag/0AYM), its quasi-affine case.
Apply that case to the dual line bundle `D⁻¹`. It gives
`D⁻¹ ≅ O(E)` for an effective Cartier divisor `E`; taking the dual
identifies `D` with the invertible ideal `O(-E) ⊆ O`. Equivalently,
a regular global section of `D⁻¹` yields the displayed monomorphism.
This translation reverses the source's positive-divisor convention.
The source's optional avoidance of a prescribed finite set is not asserted.

The registered source is
`stacks-open-line-bundle-extension-0bd9-2026-11-01`, directory SHA256
`e04f95facf97c45df0e888af89a8d92fd61988dcb397e6354110b6e4d184380d`,
retained in
`/home/taskhub/pilot/literature/Stacks Project - Open line-bundle extension and Cartier divisors, Tags 0BD9, 0BD8, 0AYM (HTML snapshot 2026-11-01)`.
The complete statement, proof and six comments of `0AYM.html` were read.
The comments discuss corrections already present in that snapshot.
No corresponding errata file was found in the bounded current Library,
private and project notes filename searches.

This module supplies only the proposition, with no proof or new axiom.
Its intended use is the local step of line-bundle extension across an open
immersion: an open subscheme of a Noetherian affine scheme is quasi-affine,
so its line bundle can first be treated as an invertible ideal.
