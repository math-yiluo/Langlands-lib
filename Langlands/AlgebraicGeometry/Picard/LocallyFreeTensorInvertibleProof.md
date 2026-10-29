# Locally free rank-one scheme modules have tensor inverses

`Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneTensorInvertible`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.LocallyFreeRankOneTensorInvertibleStatement X`
for every `X : AlgebraicGeometry.Scheme.{u}` and arbitrary universe `u`.
For an actual module sheaf `M : X.Modules`, the hypothesis is
`IsLocallyFreeRankOne M` and the conclusion is
`Langlands.CategoryTheory.TensorInvertible M`.

The tensor and unit are the published monoidal structure on actual scheme
module sheaves. The inverse witness is the actual internal-Hom dual
`Langlands.Scheme.Modules.dual M`, defined as `internalHom M O_X`.

## Implemented proof

The proof applies the published theorem
`locallyFreeRankOneDualEvaluationIsIso X M hM` from
`Langlands.AlgebraicGeometry.Picard.DualEvaluationIsoProof`. Its conclusion is
`IsIso (Langlands.Scheme.Modules.dualMonoidalEval M)`.
Installing this proved instance permits `CategoryTheory.asIso` to turn the
canonical evaluation into an isomorphism

```lean
M ⊗ Langlands.Scheme.Modules.dual M ≅ 𝟙_ X.Modules
```

The definition of `TensorInvertible M` asks for a module sheaf `N` and a
nonempty type of isomorphisms `M ⊗ N ≅ 𝟙_ X.Modules`. The proof supplies
`dual M` and the evaluation isomorphism directly, in that factor order.

The imported evaluation theorem supplies the geometric work. In
`Picard.LineBundleDualEvaluation`, `overTrivialization` transports an
open-subscheme trivialization to the category of opens contained in that
neighborhood, using `overEquiv`, `overFunctorEquiv`, and `restrictUnitIso`.
The one-element local basis and its internal-Hom coordinate functional give
compatible local generators for the sheaf and its dual. Their expansion
formulas show that sectionwise tensor evaluation is bijective on every
subopen of a trivializing neighborhood. Its inverse sends a scalar `a` to
`(a • σ) ⊗ σ^∨`.

Intersecting with arbitrary opens gives local bijectivity. The factorization
through `tensorSheafifyUnit`, together with local surjectivity of that unit,
transfers local bijectivity to `dualTensorEval`. The sheaf local-bijectivity
criterion and reflection of isomorphisms by `SheafOfModules.toSheaf` prove
that this actual sheaf morphism is invertible. Finally,
`DualEvaluationIsoProof` uses the defining comparison

```lean
dualMonoidalEval M =
  (localizedTensorIso X M (dual M)).hom ≫ dualTensorEval M
```

to obtain invertibility for the actual monoidal tensor. These published
comparisons and local arguments justify the evaluation isomorphism used
here; the final assembly adds only the existential tensor-inverse witness.

The theorem adds no geometric or finiteness hypotheses and includes the
empty scheme. It proves the forward implication only. The target statement
and its import closure are unchanged.

## Provenance

The original source is the registered retained snapshot
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
Definition 17.14.1(3) in `01C5.html` (tag 01C6) gives the local rank-one
condition. Definition 17.25.1 and Lemma 17.25.2 with proof in `01CR.html`
relate invertibility to the existence of a tensor inverse. The forward
paragraph of Lemma 17.25.4 (tag 0B8M) uses the internal-Hom dual and checks
evaluation on a trivializing cover. The imported evaluation proof implements
that local argument through sheafification, and this theorem extracts the
tensor-inverse witness. The retained passages and their proofs were read;
no source-specific errata note was found in the supplied public notes.

Worker 311 authored this assembly and its explanation. The canonical
evaluation and its invertibility are reused from the published Library by
Lean name, including Worker 530's exact-target evaluation theorem and
Worker 270's local evaluation proof. No unpublished draft is used.
