# Tensor-invertibility is equivalent to local rank one on schemes

`Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneIffTensorInvertible`
proves the exact published proposition
`Langlands.AlgebraicGeometry.Picard.LocallyFreeRankOneIffTensorInvertibleStatement X`
for every `X : AlgebraicGeometry.Scheme.{u}`, with arbitrary universe `u`.
Its conclusion is

```text
∀ M : X.Modules,
  Langlands.CategoryTheory.TensorInvertible M ↔ IsLocallyFreeRankOne M.
```

Here `X.Modules` is the actual category of scheme-module sheaves. The tensor
is the unconditional symmetric monoidal structure imported through
`Langlands.AlgebraicGeometry.Modules.TensorMonoidal`. Its comparison
`Langlands.Scheme.Modules.localizedTensorIso` identifies it with the
sheafification of sectionwise tensor, and its unit is definitionally the
structure module `SheafOfModules.unit X.ringCatSheaf`.
Tensor-invertibility means that some module sheaf `N` admits an isomorphism
`M ⊗ N ≅ 𝟙_ X.Modules`.

Local rank one is the neighborhood condition from `Picard.LineBundle`:
for every point `x : X`, there is an open `U : X.Opens` containing `x`
with an isomorphism
`M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf`.
The theorem applies to arbitrary module sheaves on arbitrary schemes,
including the empty scheme.

## Implemented proof

The proof introduces `M` and constructs the two implications of the
equivalence in the order in which the target states them.

The first implication is the published theorem
`tensorInvertibleLocallyFreeRankOne X M`, imported from
`Picard.TensorInvertibleLocallyFreeRankOneProof`. That theorem unpacks a
tensor inverse, applies `Langlands.Scheme.Modules.tensorLocalUnitFactorization`
to obtain morphisms from the structure module on a neighborhood whose
tensor is invertible, and uses
`Langlands.CategoryTheory.Picard.unitTensorCancellation` to turn the first
morphism into a trivialization. The geometric prerequisite supplies the
local finite tensor expansion, the use of the scheme's local ring to select
a unit germ, shrinking, and the actual restriction/tensor comparison.
Thus the implication returns neighborhood trivializations directly.

The second implication is the published theorem
`locallyFreeRankOneTensorInvertible X M`, imported from
`Picard.LocallyFreeTensorInvertibleProof`. It uses the proved invertibility
of `Langlands.Scheme.Modules.dualMonoidalEval M` to exhibit the actual
internal-Hom dual as a tensor inverse. The evaluation proof checks the
local rank-one calculation and transfers it through sheafification and
`localizedTensorIso` to the monoidal tensor.

This module performs only logical assembly of these two unconditional
published results. The statement and its imports are unchanged. It adds
no geometric, finiteness, or monoidal-structure parameter.

## Source and provenance

The original source is the registered retained snapshot
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
in *Stacks Project - Locally free sheaves and invertible modules,
Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)*.
The retained Definition 17.14.1(3) in `01C5.html` and Definition 17.25.1,
Lemmas 17.25.2 and 17.25.4 with their proofs in `01CR.html` were read.
No source-specific erratum was found in the supplied public notes.

[Definition 17.14.1](https://stacks.math.columbia.edu/tag/01C6) gives local
freeness of a fixed rank.
[Definition 17.25.1](https://stacks.math.columbia.edu/tag/01CS) and
[Lemma 17.25.2](https://stacks.math.columbia.edu/tag/0B8K) relate invertibility
to existence of a tensor inverse.
[Lemma 17.25.4](https://stacks.math.columbia.edu/tag/0B8M) gives the rank-one
comparison for ringed spaces with local structure-sheaf stalks, which
schemes have. The imported reverse proof uses the local unit-pairing and
cancellation route described above; the source instead uses finite
presentation to spread a stalk basis.

Worker 344 authored this logical assembly and its explanation. The
directional proofs authored by Workers 124 and 311 are reused from the
published Library by Lean name; no unpublished draft is used.
