# Tensor-invertibility and local rank one on schemes

## Statement

`Langlands.AlgebraicGeometry.Picard.LocallyFreeRankOneIffTensorInvertibleStatement
X` is the proposition

```text
∀ M : X.Modules,
  Langlands.CategoryTheory.TensorInvertible M ↔ IsLocallyFreeRankOne M.
```

Here `X : AlgebraicGeometry.Scheme.{u}` is arbitrary and `X.Modules` is Mathlib's
actual category of module sheaves. The universe follows that category's existing
conventions. There is no affine, noetherian, quasi-compact, coherent, or
quasi-coherent hypothesis, and no freely supplied monoidal instance.

The left side uses the actual symmetric monoidal sheaf tensor supplied by the
first import. Its meaning is the existence of a module sheaf `N` and an
isomorphism `M ⊗ N ≅ 𝟙_ X.Modules`. The imported unconditional instances are
`Langlands.Scheme.Modules.tensorMonoidalCategory` and
`Langlands.Scheme.Modules.tensorSymmetricCategory`. The comparison
`Langlands.Scheme.Modules.localizedTensorIso X M N` identifies the localized
tensor with `Langlands.Scheme.Modules.tensorObj M N`, the sheafification of
the sectionwise tensor; `localizedTensorNatIso X` makes this natural in both
factors. The chosen tensor unit is definitionally `structureSheaf X`, namely
`SheafOfModules.unit X.ringCatSheaf`. In the symmetric category a right tensor
inverse is also a left tensor inverse.

The right side is the published predicate from `Picard.LineBundle`: for every
point `x : X`, there is an open `U : X.Opens` containing `x` with
`Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)`.
This is an isomorphism of module sheaves on the actual open subscheme.

This file defines a proposition. It supplies no proof of either implication
and no assumption that the proposition holds.

## Original source and translation

Registered source: `stacks-local-freeness-invertibility-sections-2026-10-21`,
content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The retained folder is *Stacks Project - Locally free sheaves and invertible
modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)*.

In `01C5.html`, Definition 17.14.1(3) gives local freeness of fixed rank.
At rank one the free module is the structure module. In `01CR.html`,
Definition 17.25.1 defines invertibility through tensoring being an equivalence;
Lemma 17.25.2 identifies that condition with existence of a tensor inverse.
Lemma 17.25.4 identifies invertibility with local rank one when all
structure-sheaf stalks are local rings. The converse needs that local-ring
assumption. Every scheme has it: Mathlib's `Scheme` extends
`LocallyRingedSpace`, which includes the local-ring structure of every stalk.
Thus it is built into `X`, not omitted from the proposition.

Original links:
[Definition 17.14.1](https://stacks.math.columbia.edu/tag/01C6),
[Definition 17.25.1](https://stacks.math.columbia.edu/tag/01CS),
[Lemma 17.25.2](https://stacks.math.columbia.edu/tag/0B8K), and
[Lemma 17.25.4](https://stacks.math.columbia.edu/tag/0B8M).
The Lean statement combines the two latter equivalences and specializes to
schemes. It does not assert the additional finite-presentation or dual
identification conclusions of Lemma 17.25.2.

## Scope and proof workflow

After independent acceptance and publication of this statement, publish a
focused proof task whose target is the exact declaration above, for every
scheme and universe. Pin environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Both implications remain required.

One possible source-guided route is the following; none of these steps is
claimed as proved by this statement.

1. For a locally free rank-one module, use the existing actual internal Hom
   and dual from `Langlands.AlgebraicGeometry.ModuleDual`. Construct the sheaf
   evaluation morphism from its tensor with its dual to the structure module.
   Prove compatibility with restriction and show that evaluation is an
   isomorphism on every trivializing open, then globally. Existing sectionwise
   `dualEval` does not itself provide this tensor evaluation isomorphism.
2. For a tensor-invertible module, a route following Lemmas 17.25.2 and 17.25.4
   proves a local finite-projective presentation, identifies its stalk tensor
   inverse, uses local-ring algebra to get stalk rank one, and spreads the
   resulting basis to a neighborhood. Stalk rank one alone must not be used
   to infer local rank one without a justified spreading result; the source
   route uses finite presentation.
3. Relate any concrete tensor and unit maps used by the proof to the actual
   monoidal structure, and assemble the full equivalence.

Any substantial prerequisite needs its own precise published proposition and
proof workflow. Reuse the tensor construction in `Modules.TensorMonoidal`, the available
pullback comparisons, and the generic bridge
`Langlands.CategoryTheory.Picard.tensorInvertibilityEquivalence` from
`Langlands.CategoryTheory.Picard.TensorEquivalenceProof`. Full monoidal
pullback coherence and comparison with the earlier explicit unitors and swap
are separate obligations; this statement assumes none of them.
The existing internal Hom construction is reusable; its tensor evaluation,
local isomorphism criterion, and any needed stalk comparison must be proved
or located explicitly. This task does not duplicate the tensor construction,
the generic Picard group, or the scheme Picard specialization.
