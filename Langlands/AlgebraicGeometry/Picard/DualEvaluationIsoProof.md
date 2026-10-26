# Canonical monoidal dual evaluation for locally free rank-one sheaves

`Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneDualEvaluationIsIso`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.LocallyFreeRankOneDualEvaluationIsIsoStatement X`
for every `X : AlgebraicGeometry.Scheme.{u}` and arbitrary universe `u`.
For every actual scheme-module sheaf `M`, its sole hypothesis is
`IsLocallyFreeRankOne M`, and its conclusion is
`CategoryTheory.IsIso (Langlands.Scheme.Modules.dualMonoidalEval M)`.
The morphism has source `M ⊗ dual M` and target the actual monoidal unit.

## Implemented proof

The proof imports `Picard.LineBundleDualEvaluation` and applies its theorem
`Langlands.Scheme.Modules.isIso_dualTensorEval` to the supplied local rank-one
hypothesis. This establishes invertibility of the existing explicit evaluation
`dualTensorEval M : tensorObj M (dual M) ⟶ structureSheaf X`.
By the published definition in `ModuleDualEvaluation`, the required morphism is

```lean
(localizedTensorIso X M (dual M)).hom ≫ dualTensorEval M
```

Unfolding `dualMonoidalEval` exposes precisely this composite. The homomorphism
of `localizedTensorIso` is an isomorphism, and the preceding application makes
the explicit evaluation an isomorphism. The category-theoretic composition
instance therefore supplies invertibility of the required canonical map.

The imported evaluation proof supplies the local-to-global step. It transports
an open-subscheme trivialization to the over-category using `overEquiv`,
`overFunctorEquiv`, and `restrictUnitIso`, and uses the one-element basis and
its actual internal-Hom coordinate functional. Their expansion formulas show
that the sectionwise tensor evaluation is bijective on every subopen of a
trivializing neighborhood: its inverse sends a scalar `a` to
`(a • σ) ⊗ σ^∨`. Intersecting with any open gives local bijectivity.
The adjunction identifies that presheaf evaluation with the sheafification
unit followed by `dualTensorEval`. Local surjectivity of the sheafification
unit transfers local bijectivity to the sheaf map. Local bijectivity of a
morphism between sheaves gives an isomorphism, and the forgetful functor from
module sheaves reflects isomorphisms. This argument does not identify arbitrary
sections of a sheaf tensor with sectionwise tensors.

The new theorem adds only the comparison with the actual monoidal tensor.
It imports the published local calculation and all of its restriction and
sheafification comparisons; it assumes no evaluation or tensor-invertibility
conclusion. The argument applies to every scheme, including the empty scheme,
and adds no finiteness or geometric hypotheses. The published statement pair
and its entire import closure are unchanged.

## Provenance

The original source is the registered retained snapshot
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
In `01C5.html`, Definition 17.14.1(3), tag 01C6, rank one means local
triviality with a single generator. In `01CR.html`, the forward paragraph
of the proof of Lemma 17.25.4, tag 0B8M, checks that the canonical evaluation
is an isomorphism on a trivializing open cover. This is the step implemented
by the imported theorem. The new proof transports that result along the
published `localizedTensorIso` comparison, preserving the order `M ⊗ dual M`.
The retained section snapshots have no comments; no source-specific errata
note is present in the supplied public notes.

The local evaluation theorem and its constructions were authored by Worker 270
and are reused from the published Library by Lean name. Worker 530 authored
this exact-target monoidal wrapper and its explanation; no unpublished draft
is used.
