# Closedness, density and completeness targets for the actual right-image inverse limit

Authors: Worker 6 and Worker 1126.

This module contains statement targets only: Prop-valued definitions and
one closed master target. It proves none of them. The proof is a separate
exact-target successor task.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.1–I.1.3, printed pp.6–9/PDF12–15, were read for this module.

- I.1.1–I.1.2, printed pp.6–7/PDF12–13, supply the idempotents, their
  order and the finite local units of an idempotented ring.
- I.1.3, printed p.8/PDF14, gives the topology of `A` with zero-neighborhood
  basis `A(1-e)`. It defines `Ā` as the inverse limit of the right images
  `Ae`, with transition maps `x ↦ x e`.
- Printed p.9/PDF15 describes `Ā` as the families `ā` with `ā(e) ∈ Ae` and
  `ā(f) e = ā(e)` for `e ≤ f`. It gives `Ā` the left-translation-invariant
  topology with zero-neighborhood basis `Ā(1-e) = {ā | ā(e) = 0}`. It
  embeds `A` by `a ↦ ā`, `ā(e) = a e`.
- The same page then proves density: for every `ā`, every `e`, and every
  `f ≥ e`, `(ā - ā(f)) e = ā(e) - ā(f) e = 0`, so `ā - ā(f) ∈ Ā(1-e)`.
- Immediately afterwards the source says that it has not shown that `Ā`
  is a complete uniform space, the completion of `A`. It is not needed
  later, and it is left to the reader ("nous laissons donc cela au
  lecteur").

The registered 2010-edition errata `renard-2010-corrections-complements`
concern the pseudometric order and a local-unit formula. The 2026 text
already prints both corrections, and neither concerns density or
completeness.

## Objects used

All targets use the published constructions, imported by Lean name from
`Langlands.Algebra.IdempotentedRingRightLimit` and
`Langlands.Algebra.IdempotentedRingRightLimitUniformity`. Throughout,
`A : Type uA` is an arbitrary type with its original `NonUnitalRing A`.

- `rightCompatibleFamilies A` is the actual additive subgroup of
  `Idempotent A → A`. Its elements are the families `a` with
  `a e * e = a e` for every `e` and `a f * e = a e` whenever `e ≤ f`.
  The first equation is the source condition `ā(e) ∈ Ae`, and the second
  is the coherence `ā(f) e = ā(e)`.
- `IdempotentedRingRightLimit A` is the carrier of that subgroup, the
  source's `Ā`.
- `IdempotentedRingRightLimit.canonical` is the published canonical additive
  map `a ↦ (e ↦ a * e)`, the source's `a ↦ ā`.
- `IdempotentedRingRightLimit.discreteProductUniformSpace A` is the product
  uniformity on the full function type `Idempotent A → A`, with each factor
  discrete. It has no compatibility restriction.
- `IdempotentedRingRightLimit.uniformSpace A` is the actual family
  uniformity. It is the infimum over all idempotents `e` of the pullbacks of
  the discrete uniformity along `x ↦ x(e)`. The published module proves that
  its neighborhoods are the source's translates `b + Ā(1-e)` under
  `IsIdempotented A`. It also proves that it equals the subspace uniformity
  inherited from `discreteProductUniformSpace A`.
- `idempotentedRingUniformSpace A` is the published original uniformity on
  `A`. It is the infimum over all idempotents `e` of the pullbacks of the
  discrete uniformity along `a ↦ a * e`, the published realization of the
  source topology with zero neighborhoods `A(1-e)`.

None of these uniformities is a global instance. Each statement therefore
passes the intended topology or uniformity explicitly with `@`. This is
deliberate. Worker 6 found that leaving `IsDenseEmbedding` to instance
inference on the subtype could pick a different topology from the intended
one. With explicit arguments, no inferred or substitute topology can occur.
No statement has a topology parameter, a replacement family space, or an
assumed closedness, density or completeness certificate.

## The four statements

- `IdempotentedRingRightLimitClosedFamily A` is
  `@IsClosed (Idempotent A → A) (discreteProductUniformSpace A).toTopologicalSpace (rightCompatibleFamilies A)`.
  The actual compatible families form a closed subset of the full product
  of discrete copies of `A`. The ambient product puts no compatibility
  restriction on its families. The target does not say that the subset
  is proper. For a zero ring such as `PUnit`, every family satisfies both
  equations, so the subset is the whole product.
- `IdempotentedRingRightLimitComplete A` is
  `@CompleteSpace (IdempotentedRingRightLimit A) (IdempotentedRingRightLimit.uniformSpace A)`.
  The actual family carrier is complete for the actual family uniformity.
- `IdempotentedRingRightLimitCanonicalDense A` is `@DenseRange` of
  `canonical` into `IdempotentedRingRightLimit A`, with the topology of
  `IdempotentedRingRightLimit.uniformSpace A`. The range of `a ↦ ā` is dense
  in `Ā`.
- `IdempotentedRingRightLimitCanonicalDenseEmbedding A` is
  `@IsDenseEmbedding` of the same `canonical`. The domain carries the topology
  of `idempotentedRingUniformSpace A`, and the codomain the topology of
  `IdempotentedRingRightLimit.uniformSpace A`. The map is injective, the
  original topology of `A` is the topology induced from `Ā`, and the range
  is dense.

These four definitions are bare propositions and carry no hypothesis. The
master target below says which hypotheses each one is asserted under.

## Master target

`IdempotentedRingRightLimitDensityCompletenessTheorem` (universe `uA`) is

```
∀ (A : Type uA) [NonUnitalRing A],
  IdempotentedRingRightLimitClosedFamily A ∧
  IdempotentedRingRightLimitComplete A ∧
  (IsIdempotented A →
    IdempotentedRingRightLimitCanonicalDense A ∧
    IdempotentedRingRightLimitCanonicalDenseEmbedding A)
```

Closedness and completeness are claimed for every nonunital ring. Density
and the dense embedding are claimed only under `IsIdempotented A`, the
published finite-local-unit condition of the source. There is no global
unit, commutativity, nontriviality or countability hypothesis. Zero rings
and noncommutative nonunital rings are included.

The hypothesis is needed for the embedding. Suppose `A` is nonzero with
zero multiplication. Then `0` is its only idempotent, every coordinate
`a * 0` is `0`, and `canonical` is not injective. This example is for
explanation only and is not proved in Lean here.

## Checks in the Lean file

- Complete unapplied `example` checks give each of the five definitions its
  full type at an arbitrary universe `uA`.
- `rfl` checks show the following.
  - The full product topology is Mathlib's `Pi.topologicalSpace` with every
    factor discrete (`⊥`).
  - The closedness target is `IsClosed` of exactly the set of families
    satisfying the two compatibility equations.
  - The completeness and density targets agree with the plain Mathlib
    statements when the actual uniformities are installed locally with `let`.
- Two examples project the dense-embedding target, with the same explicit
  topologies. They give the density target, the inducing property and
  injectivity of `canonical`. This confirms that both density targets use
  the same codomain topology.
- Two examples specialize the master target. One gives the dense embedding
  of any `IsIdempotented` ring, and the other gives completeness for the
  zero ring `PUnit.{1}`.

`lean_check` inspection reports the master declaration as returning `Prop`,
with level parameter `uA`. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

- **Density** is the source's argument on printed p.9/PDF15. Under
  `IsIdempotented A` the sets `{x | x(e) = b(e)}` form the published
  neighborhood basis at a family `b`. The canonical image of `b(f)`, for any
  `f ≥ e`, lies in the set for `e`.
- **Dense embedding** combines this density with the published uniform
  embedding of `canonical` under `IsIdempotented A`. The source says only
  that the embedding is canonical and continuous. Stating it as a Mathlib
  `IsDenseEmbedding` is an internal formulation.
- **Completeness** is the reader exercise on printed p.9/PDF15. Renard prints
  no proof of it and no numbered result about it. Asserting it for every
  nonunital ring, without finite local units, is an internal strengthening.
- **Closedness** in the full discrete product is internal supporting
  mathematics for that exercise. Renard does not state it. It is not a
  premise of any other target.

The intended route is guidance only and is not a premise of any target.
Each single compatibility equation involves at most two coordinates, so it
defines a closed (indeed clopen) set in the discrete product. The compatible
families are the intersection of these sets, hence closed. A closed subset
of the complete product of discrete spaces is complete. The published equality of
`IdempotentedRingRightLimit.uniformSpace A` with the subspace uniformity
transfers this to the actual family uniformity.

## Remaining obligations

Proving the master target is a separate exact-target proof task, to be
published after this statement is accepted and published. The following
are also outside this module:

- the uniform equivalence of `Ā` with `UniformSpace.Completion` and its
  universal extension property;
- continuity of the limit multiplication;
- comparisons with annihilator quotients;
- extension of the action to arbitrary nondegenerate modules.
