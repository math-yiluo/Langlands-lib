# Relative integral closure and finiteness for supplied integer rings

Worker 107 authored the proposition
`Langlands.LocalClassField.NYLL.RelativeIntegerStructureStatement.{u,v}`.
It quantifies every prime `p`, fields `F : PadicField.{u} p` and
`E : PadicField.{v} p` in independent universes, a supplied
`Algebra F.Carrier E.Carrier`, its compatibility
`IsScalarTower (Padic p) F.Carrier E.Carrier`, and
`FiniteDimensional F.Carrier E.Carrier`. The realizations
`T : F.TopologicalData` and `S : E.TopologicalData` are arbitrary.

For these inputs the proposition states the conjunction

```lean
IsIntegralClosure S.Integers T.Integers E.Carrier ∧
  Module.Finite T.Integers S.Integers
```

The first conjunct says that inclusion of `S.Integers` into `E.Carrier` is
injective and that an element of `E.Carrier` is integral over `T.Integers`
exactly when it belongs to the image of that inclusion. The second says
that `S.Integers` is finitely generated as a module over `T.Integers`.
Both are conclusions, not assumptions.

The two local scalar choices are the published
`PadicField.TopologicalData.relativeIntegerAlgebra T S` and
`PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) T`.
The first is induced by `relativeIntegerMap T S`, the restriction of the
supplied field algebra map to the supplied integer rings. The second is
its scalar action on `E.Carrier` through `T.Integers → F.Carrier → E.Carrier`.
The algebra of `S.Integers` on `E.Carrier` is its existing inclusion algebra.
The published `relativeIntegerTower T S` certifies compatibility of these
maps; neither conjunct requires this certificate as an additional argument.
No maps, scalar structures, or global instances are defined by this module.

This is an internal, derived infrastructure target for the NYLL normalization
and inertia adapters. It is formulated directly from the existing Library
objects and Mathlib predicates, rather than transcribed from an external
source theorem. Its sole import is `Langlands.LocalField.RelativeIntegers`,
which also imports `Langlands.LocalField.Normalization.Proof`. Those modules
retain their existing authorship. The published `integers_isIntegralClosure`
and `integers_finite` in `Langlands.PadicField.TopologicalData` supply the
corresponding absolute certificates over the valuation integer ring of
`Padic p`. The private `relativeNormData` in
`Langlands.ClassFieldTheory.Local.UnitNormProof` illustrates the intended
later route: finite restriction of scalars and `IsIntegralClosure.tower_top`.
That private proof is neither imported nor copied here, and this module
contains no proof of the new proposition.

The statement imposes no Galois or unramifiedness condition and no equality
with canonical topological data. It adds no relative valuation-extension
hypothesis or conclusion; that comparison remains separate. Its two
certificates concern the exact named relative algebras, with no freely
supplied substitute algebra structures. The environment is Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
