# The lifting property of the genuine profinite integers

`Langlands.Weil.ProfiniteIntegerLifting.{u}` is a proposition stating the
following universal property. For every `G : Type u` with instances
`Group G`, `TopologicalSpace G`, `NonarchimedeanGroup G`, `CompactSpace G`,
and `T2Space G`, and every group homomorphism `f : Degree →* G`, there
exists exactly one continuous group homomorphism
`F : ProfiniteIntegers →ₜ* G` such that

```lean
F.toMonoidHom.comp frobenius.toMonoidHom = f
```

Equality here is equality of bundled homomorphisms from `Degree` to `G`.
Uniqueness is among all continuous group homomorphisms with this extension
property. The typeclass `NonarchimedeanGroup` supplies the topological group
laws and a neighborhood basis at the identity consisting of open subgroups.
Compactness and Hausdorffness are explicit hypotheses.

## Existing objects and universes

The module imports `Langlands.Weil.Pullback` and uses its definitions without
alteration. `Degree` is the small type `Multiplicative ℤ`, with its discrete
topology; `ProfiniteIntegers` is Mathlib's actual profinite completion of that
group, formed from its finite quotient groups; and `frobenius` is its canonical
integer homomorphism, bundled with continuity.

The target universe `u` is arbitrary and independent of these fixed small
source types. All target data, instances, and `f` are quantified inside the
proposition, so the declaration itself has type `Prop` and only a universe
parameter. There is no assumed extension or section, finite presentation,
countability condition, or extra smallness hypothesis on `G`. Continuity
of `f` is not an input: the integer domain already has the discrete topology.

## Provenance and scope

This is an internal derived universal-property interface for the existing
profinite completion. Its provenance is the construction and universal
property in pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean`:
`ProfiniteGrp.ProfiniteCompletion.completion`, `eta`, `lift`, `lift_eta`,
`denseRange`, and `lift_unique`. The target assumptions use
`NonarchimedeanGroup` from
`Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean`.

Mathlib's category-level `lift` places source and target in a common
universe. The present statement deliberately preserves the small completion
and permits a target in an arbitrary universe. A later proof must justify
this universe-independent extension; this module supplies no such proof.
It states the property as a `Prop`-valued definition and introduces no axiom.

The interface is intended for later Weil finite-image extension arguments.
It is not quoted as a local-field theorem, and it makes no choice of arithmetic
or geometric Frobenius. No projection density, splitting, or representation
extension theorem is asserted here.
