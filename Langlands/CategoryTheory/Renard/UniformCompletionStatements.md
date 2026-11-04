# Renard A.III.1: statements for the separated uniform completion

Author: Worker 709.

This file supplies four closed proposition definitions and their conjunction,
`Langlands.Renard.UniformCompletion.UniformCompletionStatements`.
It supplies statements only. All spaces, maps, completions and categories are
the actual Mathlib constructions.

## Original passage and convention boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The A.III.1 definition of a right universal problem is on printed251/PDF257;
example 2 is on printed252/PDF258. Both pages were read, and PDF258 was
also inspected as a rendered page.

Example 2 starts with topological vector spaces and complete topological vector
spaces, explicitly describing their morphisms as continuous maps. It then
mentions completion more generally for spaces endowed with a uniform structure.
The present statements give a precise version of that uniform generalization:
morphisms are **uniformly continuous**, and complete targets are **separated**.
These conventions are mathematical restrictions, not alternative spellings of
continuity or completeness. This unit does not assert the literal
continuous-map vector-space formulation, construct vector-space operations on
the completion, or prove a comparison with a category of continuous linear
maps.

Continuity alone does not guarantee extension to a uniform completion. For
example, the continuous function from the rationals to the reals given by
`q ↦ 1 / ((q : ℝ)^2 - 2)` has no continuous extension to the real completion:
its values are unbounded along rational points tending to `√2`. This is an
internal explanatory counterexample for the general uniform-space reading,
not a Lean result supplied by this file or an assertion attributed to Renard.
If linear maps are intended in the vector-space example, their uniform
continuity and the completion's linear structure require their own comparison.

Mathlib's completion is a separation quotient of the space of Cauchy filters.
The source space need not be separated for the extension property into complete
separated targets. Its canonical map is an embedding only under the explicit
source `T0Space` hypothesis. Thus the printed inclusion arrow is not silently
asserted for every uniform space. For uniform spaces, `T0Space` expresses
separatedness and entails the Hausdorff property.

The registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Those appendix corrections do not address this completion
example. This is a bounded errata check and does not replace the governing
2026 edition.

## Exact declarations and maps

The namespace is `Langlands.Renard.UniformCompletion`.

1. `CompletionMapStatement` quantifies over every uniform space `X`. Its
   actual `UniformSpace.Completion X` is complete and separated. The canonical
   coercion `X → Completion X` is uniformly continuous, has dense range, and
   induces the original uniform structure. If `X` is separated, this map is
   a uniform embedding. No separatedness is required of the general source.
2. `ConcreteExtensionStatement` quantifies over an arbitrary uniformly
   continuous function `f : X → Y` into a complete separated uniform space.
   The actual `Completion.extension f` is uniformly continuous and agrees
   with `f` on canonical images of points of `X`. Every uniformly continuous
   `g : Completion X → Y` with those same point values equals that extension.
   The source and target carrier universes `u` and `v` are independent.
3. `CategoricalExtensionStatement` uses the actual `UniformSpaceCat`,
   `CpltSepUniformSpace`, `UniformSpaceCat.completionFunctor`,
   `completionHom` and `extensionHom`. For every morphism `f : X → U(Y)`,
   the supplied extension satisfies
   `completionHom X ≫ U.map (extensionHom f) = f`;
   every morphism with that factorization equals the supplied extension.
   Here `U` is exactly `forget₂ CpltSepUniformSpace UniformSpaceCat`.
4. `RightUniversalStatement` says that the structured arrow built from that
   same `completionHom X` is universal for `U`. Its data-valued
   `StructuredArrow.IsUniversal` witness is wrapped in `Nonempty`.
5. `UniformCompletionStatements` conjoins items 1–4 in that order.

The categorical statements use a common arbitrary carrier universe `u`,
as do Mathlib's actual bundled categories and forgetful functor. Their object
types live in `Type (u + 1)` and their morphisms in `Type u`. The independent
target universe `v` occurs in the concrete extension statement only; this
unit does not assert a categorical functor between different carrier universes.
Empty uniform spaces are allowed. There is no compactness, metrizability,
countability, normed-space, scalar-field, or finite-dimensionality restriction.

## Provenance and implementation boundary

This is derived content: the right-universal definition is instantiated with
the actual complete-separated inclusion, and the uniform completion example is
made precise with the explicit convention corrections above. The canonical-map
properties, fixed extension and uniqueness packaging, closed conjunction, and
universe organization are internal elaborations, not four separately numbered
book assertions.

Reuse navigation was checked against Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`Mathlib/Topology/Category/UniformSpace.lean` defines both categories, the
forgetful functor, the completion and extension morphisms, and their adjunction;
`Mathlib/Topology/UniformSpace/Completion.lean` defines the actual completion,
coercion and extension and supplies their density, embedding and uniqueness
theorems. `Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean` supplies the
right-universal-arrow witness. This unit imports those definitions directly
and introduces no parallel objects or assumed completion certificates.

The exact proof of the aggregate requires its own independently reviewed
publication after this statement pair is accepted and published. The
continuous-map wording, precise topological-vector-space comparison,
linear operations and other A.III examples remain separate obligations.
