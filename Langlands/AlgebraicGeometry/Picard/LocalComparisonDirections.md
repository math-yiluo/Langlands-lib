# The two directions of the scheme local rank-one comparison

## Statements and scope

In namespace `Langlands.AlgebraicGeometry.Picard`, this module defines:

```text
LocallyFreeRankOneTensorInvertibleStatement X :=
  ∀ M : X.Modules,
    IsLocallyFreeRankOne M → Langlands.CategoryTheory.TensorInvertible M

TensorInvertibleLocallyFreeRankOneStatement X :=
  ∀ M : X.Modules,
    Langlands.CategoryTheory.TensorInvertible M → IsLocallyFreeRankOne M

LocalComparisonDirectionsStatement X :=
  LocallyFreeRankOneTensorInvertibleStatement X ∧
    TensorInvertibleLocallyFreeRankOneStatement X
```

Every declaration has complete type
`(X : AlgebraicGeometry.Scheme.{u}) → Prop`, for arbitrary universe `u`.
The final declaration selects both directions together for this statement unit.
All three declarations define propositions; none proves or assumes either
implication.

The sole import is `Langlands.AlgebraicGeometry.Picard.LocalComparisonStatement`.
The two implications split its existing
`LocallyFreeRankOneIffTensorInvertibleStatement X`, whose body quantifies over
`M : X.Modules` and asserts `TensorInvertible M ↔ IsLocallyFreeRankOne M`.
That existing declaration and its imports are unchanged.

`X.Modules` is the actual category of module sheaves on the scheme. The
monoidal instance is the actual sheaf tensor from
`Langlands.AlgebraicGeometry.Modules.TensorMonoidal`, obtained through the
imported comparison statement. `TensorInvertible M` means that a module sheaf
`N` exists with `Nonempty (M ⊗ N ≅ 𝟙_ X.Modules)`. Its tensor unit is the
structure module `SheafOfModules.unit X.ringCatSheaf`.

The imported `IsLocallyFreeRankOne M` has the exact neighborhood meaning

```text
∀ x : X, ∃ U : X.Opens, x ∈ U ∧
  Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf).
```

These are actual isomorphisms on open subschemes. There are no extra monoidal
instance parameters, affine, quasi-coherent, coherent, noetherian, or
finite-presentation hypotheses. In particular, local finite presentation is
not assumed in the converse.

## Source and provenance

This is a directional decomposition of the existing Library proposition,
specializing the Stacks comparison to schemes. Registered source:
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The retained source folder is *Stacks Project - Locally free sheaves and
invertible modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)*.

- `01C5.html`, [Definition 17.14.1(3)](https://stacks.math.columbia.edu/tag/01C6),
  specifies local freeness of fixed finite rank. At rank one the local free
  module is the structure module.
- `01CR.html`, [Definition 17.25.1](https://stacks.math.columbia.edu/tag/01CS),
  defines invertibility through the tensor functor being an equivalence.
  [Lemma 17.25.2](https://stacks.math.columbia.edu/tag/0B8K), with its proof,
  relates this to existence of a tensor inverse and derives local finite
  presentation via a local finite free direct-summand presentation.
- In the same file, [Lemma 17.25.4](https://stacks.math.columbia.edu/tag/0B8M),
  with its proof, gives local rank one implying invertibility, and the
  converse when the structure-sheaf stalks are local rings. This hypothesis
  is built into schemes through their locally ringed space structure.

The retained sections and the proofs of both cited lemmas were read.
No source-specific erratum file was present in the Library or project
`notes/errata/` locations when checked on 2026-10-24.

## Proof obligations and reuse

The source supports the forward direction by evaluation against the actual
internal-Hom dual: the sheaf tensor evaluation is an isomorphism on a
trivializing open cover, hence globally. The existing sectionwise `dualEval`
alone does not establish a sheaf tensor evaluation isomorphism. The later proof
must construct or import that morphism, justify its restriction comparisons,
and apply a justified local isomorphism criterion.

For the converse, the source first obtains local finite presentation from
the tensor inverse. Tensor/stalk comparison and local-ring algebra give stalk
rank one; finite presentation then allows a basis to extend to a neighborhood,
using the spreading result invoked as Lemma 17.11.7 in the source proof.
Stalk rank one alone does not supply the neighborhood isomorphisms required
by `IsLocallyFreeRankOne`. A different proof route remains possible if it
explicitly justifies every required tensor, restriction, and stalk comparison.

The existing modules `Modules.TensorMonoidal`, `ModuleDual`,
`Modules.SectionLocusComparison` in `Langlands.AlgebraicGeometry`, and
`Langlands.CategoryTheory.Picard.TensorEquivalenceProof` supply reusable
infrastructure. This statement unit introduces none of those constructions.
Tensor evaluation is a separate prerequisite and is unnecessary to formulate
these propositions.

After independent statement acceptance and Library publication, Worker 344
will arrange the two exact-target proof tasks and assembly of the original
iff in parent task `45730c00-045d-4204-bf5f-1f49e61f733b`. Publishing these
statements proves neither direction and does not complete that parent task.

Worker 368 prepared this pair from Worker 344's directional specification and
source workflow.
