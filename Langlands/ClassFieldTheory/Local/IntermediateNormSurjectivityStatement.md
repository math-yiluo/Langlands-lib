# Inheritance of all intermediate-field norm surjectivity

Worker 107 authored this statement. The declaration
`Langlands.ClassFieldTheory.Local.IntermediateNormSurjectivityInheritance.{u}`
is a `Prop`-valued definition. It states an internal consequence of finite-extension
norm algebra; this module does not prove it.

## Statement and scope

For arbitrary fields `K L : Type u`, with a specified `Algebra K L` and
`FiniteDimensional K L`, assume that for every `E : IntermediateField K L`
the norm `N_{L/E} : Lˣ → Eˣ` is surjective. The finite-dimensional instance
in this premise is `FiniteDimensional.right K E L`.

The conclusion is a right-associated conjunction, in this order:

1. `N_{L/K} : Lˣ → Kˣ` is surjective.
2. For every `E : IntermediateField K L`, `N_{E/K} : Eˣ → Kˣ` is surjective.
3. For every `E : IntermediateField K L` and every
   `F : IntermediateField K E`, `N_{E/F} : Eˣ → Fˣ` is surjective.
4. For every `E : IntermediateField K L` and every
   `F : IntermediateField E L`, `N_{L/F} : Lˣ → Fˣ` is surjective.

The universe `u` is arbitrary and shared by `K` and `L`. Every intermediate
field is quantified, including the bottom and top fields. There are no Galois,
separability, cyclicity, characteristic, local-field, topology, or cohomology
hypotheses. Here `Eˣ` is the full multiplicative group of the field, not a
valuation-ring unit group. In particular, clause 3 supplies the entire
intermediate-field norm-surjectivity family for `E/K`, and clause 4 supplies
that family for `L/E`.

## Norms and scalar structures

Every norm is the existing `Langlands.LocalClassField.normUnits` from
[`Norms`](Norms.md), defined as `Units.map (Algebra.norm K)` for the relevant
base field `K`. Thus the maps are the determinant norms of multiplication.
No arbitrary homomorphism or norm image replaces them.

For `E : IntermediateField K L`, its field structure and the maps `K → E → L`
are Mathlib's canonical subtype structures, with their canonical scalar tower.
Clause 2 installs `FiniteDimensional.left K E L`. In clause 3 the field `F`
is a subtype of `E`; its maps `K → F → E` are again canonical. That clause
first installs `FiniteDimensional.left K E L` and then
`FiniteDimensional.right K F E`. These are consequences of the single supplied
finite-dimensionality assumption on `L/K`, not additional hypotheses.

In clause 4, `F` is an intermediate field of `L/E`. The canonical structures
give the tower `K → E → F → L`. The intermediate field
`F.restrictScalars K : IntermediateField K L` has the same carrier, field
structure, and inclusion in `L` as `F`. The explicit instance
`FiniteDimensional.right K (F.restrictScalars K) L` therefore has the required
type `FiniteDimensional F L`. Restriction of scalars changes the base-field
presentation, not the norm `N_{L/F}`.

## Derived provenance and proof boundary

This is an internal algebraic prerequisite for the finite p-group norm/H2
argument, isolated at Worker 28's request. It is not a quotation or a new
literature theorem. Its provenance is the published determinant-norm
construction, Mathlib's `Algebra.norm_norm`, and the canonical intermediate-field
operations in `Mathlib.FieldTheory.IntermediateField`.

The mathematical derivation is as follows. The premise at the bottom field,
transported along `IntermediateField.botEquiv`, yields clause 1. Norm
transitivity then yields clause 2. For clause 3, map `F` into `L` using
`IntermediateField.lift` (equivalently `F.map E.val`), identify it with `F`
using `IntermediateField.liftAlgEquiv`, and apply the assumed norm surjectivity
and transitivity in the resulting tower. For clause 4, apply the premise to
`F.restrictScalars K`. Norm compatibility under these canonical equivalences
is supported by Mathlib's `Algebra.norm_eq_of_ringEquiv`.

These are the provenance and intended derivation, not implemented proofs in
this pair. The proof of this exact proposition and its cohomological
applications remain separate tasks. No imported Library pair is modified.
