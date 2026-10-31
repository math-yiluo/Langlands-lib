# Closedness, density and completeness targets for the actual left-image module inverse limit

Authors: Worker 6 and Worker 1125.

This module contains statement targets only: four Prop-valued definitions
and one closed master target. It proves none of them. The proof is a
separate exact-target successor task.

Worker 6 wrote the first draft of the four predicates and the master
target. Worker 1125 checked it against the source, flattened the master
into four conjuncts with the same hypotheses, and added the
unequal-universe checks, the topology-body checks, the projections and the
specializations listed below.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.1–I.1.4, printed pp.6–10/PDF12–16, were read for this module.

- I.1.1–I.1.2, printed pp.6–7/PDF12–13, supply the idempotents, their
  order, the finite local units of an idempotented ring and nondegenerate
  modules (every vector is fixed by some idempotent).
- I.1.3, printed p.9/PDF15, treats the ring itself. It proves that `A` is
  dense in the right-image limit `Ā`: for every `ā`, every `e` and every
  `f ≥ e`, `ā - ā(f)` lies in the zero neighborhood `Ā(1-e)`. Immediately
  afterwards it says that it has not shown that `Ā` is a complete uniform
  space, the completion of `A`, and leaves this to the reader ("nous
  laissons donc cela au lecteur").
- I.1.4, "Complété d'un module non dégénéré", printed p.9/PDF15, starts
  from a nondegenerate module `M` over the idempotented ring `A`. It says
  that the proofs of the assertions that follow adapt easily from the
  previous section ("s'adaptent facilement"). It gives `M` the
  translation-invariant uniformity with zero-neighborhood basis
  `(1-e)·M = {m - e·m}`, and the pseudometrics `d_e`. It then says that
  the completion of `M` for this uniformity is the inverse limit
  `lim e·M` with transition maps `m ↦ e·m` for `e ≤ f`. This limit is
  described as the families `m̄` with `m̄(e) ∈ e·M` and `e·m̄(f) = m̄(e)`
  for `e ≤ f`, and `M` embeds in it by `m ↦ m̄`, `m̄(e) = e·m`.
- Printed p.10/PDF16 continues with the Hom comparison
  `Hom_A(A, M) ≅ M̄` and the `A`-module structure on `M̄`. These are not
  used here.

So the source asserts, without a separate proof, that the module limit is
the completion and that `M` embeds in it. For the ring, it proves only
density and explicitly leaves completeness to the reader. Renard prints no
module completeness proof and no closedness statement.

## Objects used

All targets use the published constructions, imported by Lean name from
`Langlands.Algebra.NonUnitalModuleLeftLimit`,
`Langlands.Algebra.NonUnitalModuleUniformity` and
`Langlands.Algebra.NonUnitalModuleLeftLimitUniformity`. Throughout,
`A : Type uA` and `M : Type uM` lie in independent universes, with their
original `NonUnitalRing A`, `AddCommGroup M` and `NonUnitalModule A M`.

- `leftCompatibleFamilies A M` is the actual additive subgroup of
  `Idempotent A → M`. Its elements are the families `x` with
  `e • x e = x e` for every `e` and `e • x f = x e` whenever `e ≤ f`.
  The first equation is the source condition `m̄(e) ∈ e·M`, and the second
  is the coherence `e·m̄(f) = m̄(e)`.
- `NonUnitalModuleLeftLimit A M` is the carrier of that subgroup, the
  source's `M̄`. No scalar action is installed on it.
- `NonUnitalModuleLeftLimit.canonical` is the published canonical additive
  map `m ↦ (e ↦ e • m)`, the source's `m ↦ m̄`.
- `NonUnitalModuleLeftLimit.discreteProductUniformSpace A M` is the product
  uniformity on the full function type `Idempotent A → M`, with each factor
  discrete. It has no compatibility restriction.
- `NonUnitalModuleLeftLimit.uniformSpace A M` is the actual family
  uniformity. It is the infimum over all idempotents `e` of the pullbacks
  of the discrete uniformity along `x ↦ x(e)`. The published module proves
  that it equals the subspace uniformity inherited from
  `discreteProductUniformSpace A M`.
- `nonUnitalModuleUniformSpace A M` is the published original uniformity on
  `M`. It is the infimum over all idempotents `e` of the pullbacks of the
  discrete uniformity along `m ↦ e • m`. Its zero neighborhood for `e` is
  the kernel of `m ↦ e • m`, which the published module identifies with the
  source's `(1-e)·M`. The published `comap_canonical` says it is the
  pullback of the family uniformity along `canonical`.

None of these uniformities is a global instance. Each statement therefore
passes the intended topology or uniformity explicitly with `@`. This is
deliberate: with two local uniformities installed by `let`, instance
inference on the subtype picked a different codomain topology for
`IsDenseEmbedding` than the intended one. With explicit arguments, no
inferred or substitute topology can occur. No statement has a topology
parameter, a replacement family space, or an assumed closedness, density or
completeness certificate.

## The four statements

- `NonUnitalModuleLeftLimitClosedFamily A M` is
  `@IsClosed (Idempotent A → M) (discreteProductUniformSpace A M).toTopologicalSpace (leftCompatibleFamilies A M)`.
  The actual compatible families form a closed subset of the full product
  of discrete copies of `M`. The target does not say that the subset is
  proper. For the zero action every compatible family is `0`, and for the
  trivial carrier the subset is the whole product.
- `NonUnitalModuleLeftLimitComplete A M` is
  `@CompleteSpace (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit.uniformSpace A M)`.
  The actual family carrier is complete for the actual family uniformity.
- `NonUnitalModuleLeftLimitCanonicalDense A M` is `@DenseRange` of
  `canonical` into `NonUnitalModuleLeftLimit A M`, with the topology of
  `NonUnitalModuleLeftLimit.uniformSpace A M`. The range of `m ↦ m̄` is
  dense in `M̄`.
- `NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M` is
  `@IsDenseEmbedding` of the same `canonical`. The domain carries the
  topology of `nonUnitalModuleUniformSpace A M`, and the codomain the
  topology of `NonUnitalModuleLeftLimit.uniformSpace A M`. The map is
  injective, the original topology of `M` is the topology induced from
  `M̄`, and the range is dense.

These four definitions are bare propositions and carry no hypothesis. The
master target below says which hypotheses each one is asserted under.

## Master target

`NonUnitalModuleLeftLimitDensityCompletenessTheorem` (universes `uA`, `uM`)
is

```
∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
  NonUnitalModuleLeftLimitClosedFamily A M ∧
  NonUnitalModuleLeftLimitComplete A M ∧
  (IsIdempotented A → NonUnitalModuleLeftLimitCanonicalDense A M) ∧
  (IsIdempotented A → IsNondegenerate A M →
    NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M)
```

- Closedness and completeness are claimed for every original nonunital
  module, with no hypothesis on `A` or `M`.
- Density is claimed under `IsIdempotented A` only, the published
  finite-local-unit condition. No nondegeneracy of `M` is assumed.
- The dense embedding is claimed under `IsIdempotented A` and
  `IsNondegenerate A M`, the published condition that every vector is fixed
  by some idempotent.

There is no unit-action law, global unit, field, commutativity,
nontriviality, countability, dimension or finiteness hypothesis. Zero
rings, zero actions and trivial carriers are included.

Nondegeneracy is needed for the embedding. Take any nonzero `M` with the
zero action of an idempotented ring. Every coordinate `e • m` is `0`, so
`canonical` is the zero map and is not injective. This example is for
explanation only and is not proved in Lean here. The density target still
applies to it: its family carrier is `{0}`.

## Checks in the Lean file

- Complete unapplied `example` checks give each of the five definitions its
  full type at arbitrary independent universes `uA`, `uM`, and at both
  unequal assignments `(0,1)` and `(1,0)`.
- `rfl` checks give the master body at `(uA, uM)`, `(0,1)` and `(1,0)`.
- Topology-body checks show the following.
  - The full product topology is, by `rfl`, Mathlib's `Pi.topologicalSpace`
    with every factor discrete (`⊥`).
  - The family topology is the infimum over `e` of the topologies induced
    by `x ↦ x(e)` from the discrete topology, by
    `UniformSpace.toTopologicalSpace_iInf`. It is also the subtype topology
    of the full discrete product, by `uniformSpace_eq_subtype`.
  - The original topology on `M` is the infimum over `e` of the topologies
    induced by `m ↦ e • m` from the discrete topology, again by
    `UniformSpace.toTopologicalSpace_iInf`.
- Predicate-body checks by `rfl` show the following.
  - The closedness target is `IsClosed` of exactly the set of families
    satisfying the two compatibility equations.
  - The completeness and density targets agree with the plain Mathlib
    statements when the actual uniformity is installed locally with `let`.
  - The dense-embedding target is `@IsDenseEmbedding` with both infimum
    uniformities written out explicitly.
  - `canonical m` has coordinate `e • m` at `e`.
- Two examples project the dense-embedding target, with the same explicit
  topologies. They give the density target, the inducing property and
  injectivity of `canonical`. This confirms that both density targets use
  the same codomain topology.
- Five examples specialize the master target:
  - density and dense embedding for an idempotented ring and a
    nondegenerate module;
  - closedness and completeness for the zero action of any nonunital ring;
  - density for the zero action of an idempotented ring;
  - completeness for the zero ring `PUnit.{1}` acting on `PUnit.{2}`;
  - the dense embedding for an ordinary unital module, through
    `NonUnitalModule.ofModule`, `IsIdempotented.of_ring` and the idempotent
    `1`.

`lean_check` inspection reports the master declaration as returning `Prop`,
with level parameters `uA` and `uM`. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

- **Completeness** corresponds to I.1.4's claim, printed p.9/PDF15, that
  the module limit is the completion of `M`. The source proves nothing
  here beyond saying that the I.1.3 arguments adapt, and for the ring it
  leaves completeness to the reader. Asserting completeness for every
  original module, without finite local units or nondegeneracy, is an
  internal strengthening.
- **Density** adapts the I.1.3 ring argument on the same page. Asserting it
  without nondegeneracy of `M` is internal: the source works only with
  nondegenerate modules.
- **Dense embedding** corresponds to the source's statement that `M` embeds
  in its completion. The source says only "se plonge". Stating it as a
  Mathlib `IsDenseEmbedding` for the published original uniformity is an
  internal formulation. Its hypotheses are the source's: an idempotented
  ring and a nondegenerate module.
- **Closedness** in the full discrete product is internal supporting
  mathematics for completeness. Renard does not state it. It is not a
  premise of any other target.

The intended route is guidance only and is not a premise of any target.
Each single compatibility equation involves at most two coordinates, so it
defines a closed (indeed clopen) set in the discrete product. The
compatible families are the intersection of these sets, hence closed. A
closed subset of the complete product of discrete spaces is complete. The
published equality of `NonUnitalModuleLeftLimit.uniformSpace A M` with the
subspace uniformity transfers this to the actual family uniformity. For
density, a family `x` is approximated in its `e` coordinate by
`canonical (x f)` for any `f ≥ e`, since `e • x f = x e`. Finite upper
bounds from `IsIdempotented A` reduce finitely many coordinate conditions
to one. Nondegeneracy then adds injectivity through the published
`canonical_injective`, and the published `isUniformInducing_canonical`
supplies the inducing property.

## Remaining obligations

Proving the master target is a separate exact-target proof task, to be
published after this statement is accepted and published. The following
are also outside this module:

- the uniform equivalence of `M̄` with `UniformSpace.Completion` for the
  original uniformity, and its universal extension property;
- the module pseudometrics `d_e`;
- the comparison `Hom_A(A, M) ≅ M̄` and the `A`-module structure on `M̄`;
- the completion functor and the smoothing/completion adjunction of I.1.5.
