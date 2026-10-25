# Canonical dual evaluation for locally free rank-one scheme modules

For every `X : AlgebraicGeometry.Scheme.{u}`, the proposition definition
`Langlands.AlgebraicGeometry.Picard.LocallyFreeRankOneDualEvaluationIsIsoStatement X`
has exactly the content

```lean
∀ M : X.Modules,
  Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne M →
    CategoryTheory.IsIso (Langlands.Scheme.Modules.dualMonoidalEval M)
```

Here `M` is an actual scheme-module sheaf. The imported predicate
`IsLocallyFreeRankOne M`, defined in
`Langlands.AlgebraicGeometry.Picard.LineBundle`, says that each point of `X`
has an open neighborhood `U` for which the actual restriction `M.restrict U.ι`
is isomorphic to `SheafOfModules.unit U.toScheme.ringCatSheaf`.
This is the rank-one case of the neighborhood definition in Stacks Project
Definition 17.14.1(3), with a singleton direct sum identified with the
structure sheaf.

## The specified evaluation map

The conclusion concerns the published canonical map
`Langlands.Scheme.Modules.dualMonoidalEval M : M ⊗ dual M ⟶ 𝟙_ X.Modules`,
defined in `Langlands.AlgebraicGeometry.ModuleDualEvaluation`.
The left factor is `M`; the right factor is its actual internal-Hom dual,
`dual M = internalHom M (Langlands.SchemeModule.structureModule X)`.
The tensor and unit are the actual monoidal tensor and structure-sheaf unit
on `X.Modules`.

In the namespace `Langlands.Scheme.Modules`, the published definition is

```lean
dualMonoidalEval M :=
  (localizedTensorIso X M (dual M)).hom ≫ dualTensorEval M
```

The published comparison `localizedTensorIso X M (dual M)` identifies
`M ⊗ dual M` with the explicit sheafified tensor `tensorObj M (dual M)`.
The published `dualTensorEval M` swaps the factors using `tensorComm` and
then applies `internalHomTensorEval M (Langlands.SchemeModule.structureModule X)`.
Its formula on the sheafification images of elementary tensors is
`m ⊗ φ ↦ φ(m)`, as recorded by
`dualTensorEval_app_tensorSheafifyUnit`.
The published identity `localizedTensorIso_inv_dualMonoidalEval` recovers
this explicit evaluation from the monoidal one. This module imports these
constructions without reimplementing them.

## Source and scope

This is the scheme specialization of the evaluation-isomorphism step in the
proof of Stacks Project Lemma 17.25.4, tag
[0B8M](https://stacks.math.columbia.edu/tag/0B8M).
That proof considers the map
`𝓛 ⊗ Hom(𝓛, 𝒪_X) → 𝒪_X` and checks that it is an isomorphism
on an open cover trivializing the locally free rank-one sheaf `𝓛`.
The rank-one premise follows Definition 17.14.1(3), tag
[01C6](https://stacks.math.columbia.edu/tag/01C6).
The registered retained source is
`stacks-local-freeness-invertibility-sections-2026-10-21`,
content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The exact locators are `01CR.html`, Section 17.25, proof of Lemma 17.25.4,
the paragraph beginning with local freeness of rank one; and `01C5.html`,
Section 17.14, Definition 17.14.1(3), in the retained HTML snapshot of
2026-10-21.

The file defines a proposition and supplies no proof of local evaluation
invertibility, compatibility with restriction, or detection of isomorphisms
from local data. It introduces no additional constructions or hypotheses.
In particular, tensor invertibility, invertibility of evaluation, and local
freeness of the dual are not premises. There are no affine, noetherian,
quasi-compact, coherence, quasicoherence, or finite-presentation assumptions.
The statement does not assert an unspecified map exists and does not prove
the forward tensor-invertibility implication or the final local comparison.
