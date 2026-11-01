# Noetherian finite-surjective descent of affineness

Authors: Worker 208 and Worker 239.

This module defines the proposition corresponding to Stacks Project
[Lemma 69.17.3, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP):
a finite surjective morphism of algebraic spaces with affine source and
Noetherian target has affine target. It uses the published
`SchemeLocalGeometry` and `Basic` interfaces unchanged. The target's
Noetherian condition is expressed by a scheme chart; the comparison with
Stacks' convention is explained below. This module states the proposition
and supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianFiniteSurjectiveAffineDescentStatement.{u}`.
Its defining formula is

```lean
def NoetherianFiniteSurjectiveAffineDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsFinite (hom f) → IsSurjective (hom f) →
      IsRepresentedByAffineScheme X →
      (∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ Y.presheaf),
          IsEtale a ∧ IsSurjective a ∧ IsNoetherian U.left) →
      IsRepresentedByAffineScheme Y
```

The universe `u` is arbitrary. The universal quantifiers range over every
base scheme `S : Scheme.{u}`, every pair of actual algebraic spaces `X`
and `Y` over `S`, and every actual morphism `f : X ⟶ Y`. Algebraic spaces
use the fppf-sheaf convention of `Basic`, with presheaf values in
`Type (u + 1)`. The transformation `hom f` is the morphism's underlying
map of presheaves.

The first two hypotheses use the existing relative scheme-test predicates
`IsFinite` and `IsSurjective`. Each includes representability and tests
every represented scheme pullback. More explicitly, for all `T V : Over S`,
all `g : (schemeYoneda S).obj T ⟶ Y.presheaf`,
all `b : (schemeYoneda S).obj V ⟶ X.presheaf`, and every `p : V ⟶ T`
with `IsPullback b ((schemeYoneda S).map p) (hom f) g`, the projection
`p.left` must be finite, respectively surjective, as a scheme morphism.
Surjectivity is geometric surjectivity on points of these projections.

`IsRepresentedByAffineScheme X` supplies an actual `V : Over S`,
`AlgebraicGeometry.IsAffine V.left`, and
`Nonempty ((schemeYoneda S).obj V ≅ X.presheaf)`. The conclusion asks
for the corresponding witnesses for `Y`. Affineness is absolute
affineness of the representing scheme. The structure map to `S` is
arbitrary.

The chart hypothesis supplies an actual scheme `U` over `S` and an actual
natural transformation
`a : (schemeYoneda S).obj U ⟶ Y.presheaf`, satisfying `IsEtale a`,
`IsSurjective a`, and Mathlib's `AlgebraicGeometry.IsNoetherian U.left`.
The first two predicates again include representability and require that
every represented scheme projection be étale, respectively surjective.
These are exactly the chart conditions used in `Basic`. Mathlib's
`IsNoetherian` is locally Noetherian plus `CompactSpace` for the underlying
scheme; see `Mathlib/AlgebraicGeometry/Noetherian.lean`, the class
`AlgebraicGeometry.IsNoetherian`, in the environment's pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. The chart `U` need
not be affine.

## Original source and Noetherian convention

The main registered source is
`stacks-noetherian-space-affine-descent-2026-11-01`, the retained Stacks
Project HTML snapshot of 1 November 2026, with directory SHA-256
`6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`.
The originals and same-stem text aids are retained in the literature folder
beginning `Stacks Project - Noetherian finite-surjective affineness and
Noetherian algebraic spaces`.

In `07VP.html`, Lemma 69.17.3 uses the letters `f : Y → X`, with affine
source `Y` and Noetherian target `X`. The Lean formula exchanges those
letters, using source `X` and target `Y`. Its finite, surjective and
affine-representability predicates are the published interfaces documented
in `SchemeLocalGeometry` and `FiniteSurjectiveAffineDescentStatement`.
In particular, the representability included in `IsSurjective (hom f)`
is already supplied by `IsFinite (hom f)`.

Stacks [Definition 66.24.1, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA),
in `03EA.html` and Section 66.24 (`03E9.html`), defines a Noetherian
algebraic space to be quasi-compact, quasi-separated and locally
Noetherian. The chart hypothesis in this formula expresses exactly
quasi-compactness and local Noetherianity:

- [Definition 66.5.1, Tag 03E2](https://stacks.math.columbia.edu/tag/03E2)
  defines quasi-compactness by a surjective étale chart from a
  quasi-compact scheme.
- [Lemma 66.7.1, Definition 66.7.2 and Remark 66.7.3, Tag 03E5](https://stacks.math.columbia.edu/tag/03E5)
  identify local Noetherianity with that property on some, equivalently
  every, étale-surjective scheme chart.
- Conversely, choose a quasi-compact étale-surjective chart of a
  quasi-compact locally Noetherian space. Local Noetherianity holds on
  that chart, making its scheme Noetherian. This argument is also given
  by Elías Guisado in comment #11687 (27 July 2026) on
  [Section 66.24, Tag 03E9](https://stacks.math.columbia.edu/tag/03E9).

The chart condition alone therefore omits the quasi-separatedness in
Stacks' definition. Under the other hypotheses, that property follows:
finiteness makes `f` affine and universally closed, while the affine
source is absolutely separated. Stacks
[Lemma 67.9.8(2), Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2),
retained as `05Z2.html` in the main source, makes the target absolutely
separated, hence quasi-separated. Absolute separatedness here refers to
the space itself; it imposes no separatedness requirement on its structure
morphism to the arbitrary base `S`.

For the finiteness implication, the second registered source is
`stacks-algebraic-space-affine-descent-2026-11-01`, directory SHA-256
`10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`:
`03ZN.html`, [Lemma 67.45.7, Tag 0415](https://stacks.math.columbia.edu/tag/0415).
The first paragraph of the proof of Lemma 70.15.1 in its `07VQ.html`
uses this same separatedness argument.

Thus the written chart hypothesis is weaker than literal Stacks
Noetherianity, and is equivalent to it in the presence of the other
hypotheses of this statement. This is the literature justification for
the chosen formulation; the module proves no Lean comparison theorem.
The six main-source pages and their comments were read. `07VP`, `03EA`,
`03E2`, `03E5` and `05Z2` have no comments. Section `03E9` has comments
#11687 and #11688; the latter's stronger chart claim is unnecessary here.
No source-specific errata note was found in the checked project, Library
or workspace locations.

## Scope

The only new declaration is this Prop-valued statement definition. Its
formula adds just the displayed chart hypothesis to the published
`FiniteSurjectiveAffineDescentStatement`. It assumes no finite
presentation, flatness, reducedness, separatedness or quasi-separatedness,
no condition on the base, no affine chart, and no prior scheme
representation of `Y`. Every published Lean/Markdown pair and its import
closure remains unchanged.

The proof of this proposition is a separate successor unit. The
Noetherian-approximation reduction for the unrestricted statement remains
with task `490ff2e9-c8ce-4d2c-a051-cd6d2ba2c025`; neither that reduction
nor the Noetherian descent theorem is proved here.
