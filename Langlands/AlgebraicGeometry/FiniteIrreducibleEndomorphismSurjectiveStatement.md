# Surjectivity of finite endomorphisms of irreducible Noetherian schemes

`Langlands.AlgebraicGeometry.FiniteIrreducibleEndomorphismSurjectiveStatement`
is a `Prop`-valued definition. For every universe `u`, every scheme
`X : Scheme.{u}` with `TopologicalSpace.NoetherianSpace X` and
`IrreducibleSpace X`, and every endomorphism `f : X ⟶ X`, it states

```text
IsFinite f → Surjective f.
```

All predicates are Mathlib's actual predicates. `NoetherianSpace X` concerns
the underlying topological space: its open subsets satisfy the ascending-chain
condition, equivalently its closed subsets satisfy the descending-chain
condition. It does not require Noetherian local rings. `IrreducibleSpace X`
includes nonemptiness. `IsFinite f` means a finite morphism of schemes: inverse
images of affine opens are affine and their induced ring maps are finite.
`AlgebraicGeometry.Surjective f` means that the underlying function on scheme
points is surjective.

The declaration retains arbitrary universes and assumes no base field or
structure morphism. It imposes no reducedness, properness, dimension bound,
group structure, dominance, flatness, surjectivity, or image certificate.
Sobriety and the separation property `T0Space` of the point space are
properties of schemes, rather than additional hypotheses.

## Internal derived provenance

This is an internal general lemma formulated for the Library's
`Langlands.GroupScheme.FieldFiniteEndomorphismSurjectiveStatement`. It is
derived from elementary scheme topology and the properties of finite
morphisms; it is not presented as a transcription of an external theorem.
The generic-point argument below was proposed in the task context supplied by
Worker 414. In particular, this general statement is not attributed to
Milne's Proposition 8.1 about abelian varieties.

The statement does not assume or import
`Langlands.GroupScheme.FieldFiniteEndomorphismSurjectiveStatement` or
`Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement`. An application to
those settings must separately establish the topological hypotheses.

## Possible noncircular proof route

The following argument explains the intended mathematical content and a
possible route for the separate proof task. It is not a Lean proof in this
module.

1. Let `η` be the generic point of `X`, available because schemes are sober
   and `X` is irreducible. It specializes to every point, in particular to
   `f(η)`. Continuity gives
   `aₙ ⤳ aₙ₊₁` for `aₙ = fⁿ(η)`.

2. A finite scheme morphism is locally quasi-finite and quasi-compact; its
   point fibres are finite discrete subspaces. The discrete property is
   essential here: cardinal finiteness alone does not exclude distinct
   comparable points in a non-Hausdorff space. If `x ⤳ y` and
   `f(x) = f(y)`, then `x` and `y` belong to the same discrete fibre, so
   `x = y`. Thus `f` cannot identify distinct points related by
   specialization.

3. Suppose `η ≠ f(η)`. Every consecutive pair `aₙ, aₙ₊₁` is then distinct:
   an equality at a later step can be pulled back one step using the preceding
   discrete-fibre property, repeatedly giving `η = f(η)`. Specialization
   yields
   `closure {aₙ₊₁} ⊆ closure {aₙ}`. These inclusions are strict, since equality
   of singleton closures in the `T0` point space of a scheme would give
   `aₙ₊₁ = aₙ`. They form an infinite strictly descending chain of closed
   subsets, contradicting `NoetherianSpace X`. Consequently `f(η) = η`.

4. A finite morphism is closed, so its range is closed. That range contains
   `η = f(η)` and therefore contains `closure {η} = X`. Hence the underlying
   point map is surjective.

At the pinned Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`, the relevant interfaces are:

- `Mathlib/Topology/NoetherianSpace.lean`: the instance
  `WellFoundedLT (TopologicalSpace.Closeds X)` expressing the descending-chain
  obstruction;
- `Mathlib/Topology/Sober.lean`: `genericPoint_specializes` and
  `genericPoint_closure`;
- `Mathlib/Topology/DiscreteSubset.lean`: `IsDiscrete.eq_of_specializes`;
- `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`: the instance from
  `IsFinite` to `LocallyQuasiFinite`, and
  `Scheme.Hom.isDiscrete_preimage_singleton` and
  `Scheme.Hom.finite_preimage_singleton`;
- `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`,
  `Integral.lean`, and `UniversallyClosed.lean`: finite morphisms are integral,
  hence universally closed, giving `Scheme.Hom.isClosedMap`.

The argument uses neither a dimension comparison nor the abelian-scheme
surjectivity or isogeny assertions it is intended to help prove.

## Separate proof obligation

This module defines the proposition and proves no instance of it. The
successor must prove this exact proposition in every universe, with no
additional hypotheses, supplied proof certificate, proof holes, or new
axioms. The topology steps above remain obligations of that proof. Any small
helpers specific to this route can stay with the proof; substantial reusable
prerequisites require duplicate searches and focused tasks in dependency
order.
