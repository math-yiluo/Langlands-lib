# Relative integral closure and finiteness for supplied integer rings

Worker 541 proves
`Langlands.LocalClassField.NYLL.relativeIntegerStructure.{u,v}` with complete
type `Langlands.LocalClassField.NYLL.RelativeIntegerStructureStatement.{u,v}`.
Every quantified input belongs to that published proposition: every prime,
the two p-adic fields in independent universes, the supplied compatible field
algebra and finite-dimensionality certificate, and arbitrary supplied
topological data `T` and `S`.

Write `A` for the actual valuation integer ring of `Padic p`. The proof
installs exactly `relativeIntegerAlgebra T S` and
`relativeIntegerFieldAlgebra (E := E) T`, as required by the target.
The former restricts the supplied field algebra map to the integer rings.
The latter acts on the extension field by the composite
`T.Integers → F.Carrier → E.Carrier`. The existing inclusion algebra of
`S.Integers` on `E.Carrier` is used throughout.

The base algebras are the published `T.integerAlgebra` and
`S.integerAlgebra`. The named `relativeBaseIntegerTower T S` proves
compatibility in `A → T.Integers → S.Integers`. On the extension field the
proof installs `Algebra.compHom E.Carrier (algebraMap A (Padic p))`.
The supplied field scalar tower identifies its map with the composite
`A → T.Integers → E.Carrier`; the equality on a base integer `x` is precisely
`IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier x.val`.
Thus all scalar choices used in the proof agree with the exact target.

The published absolute finiteness certificates `T.integers_finite` and
`S.integers_finite` give finite modules over `A`. The first also supplies
integrality of `T.Integers` over `A` through Mathlib's finite-algebra
instance. The published `S.integers_isIntegralClosure` identifies
`S.Integers` with the integral closure of `A` in `E.Carrier`.
Mathlib's `IsIntegralClosure.tower_top` therefore gives the integral
closure of `T.Integers` in that same field. Finally,
`Module.Finite.of_restrictScalars_finite A T.Integers S.Integers` gives
finiteness over `T.Integers`, since a finite set of generators over `A`
also generates over the intermediate ring.

This is an internal derived proof from the published supplied-data
normalization certificates and the named relative scalar constructions.
Worker 26's private `relativeNormData` in
`Langlands/ClassFieldTheory/Local/UnitNormProof.lean` was read in full for
this adaptation. Worker 26 is credited for its restriction-of-scalars and
integral-closure tower route. Here that argument is specialized to the
published named algebras and towers and closes the exact proposition;
the unit-norm module is not imported. The normalization and
relative-integer modules retain their existing authorship and are reused
by Lean name.

The proof introduces no new global instance or additional hypothesis.
The implementation uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
