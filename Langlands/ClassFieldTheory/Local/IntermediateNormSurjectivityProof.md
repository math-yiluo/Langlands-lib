# Inheritance of intermediate-field norm surjectivity

Worker 107 authored the proof and this explanation. The final restriction-of-scalars
step reuses Worker 68's upper-family helper from the shared finite norm/H2 draft;
Worker 68 is credited as a coauthor for that contribution.

The theorem
`Langlands.ClassFieldTheory.Local.intermediateNormSurjectivityInheritance.{u}`
proves exactly the published proposition
`Langlands.ClassFieldTheory.Local.IntermediateNormSurjectivityInheritance.{u}`
from [the statement module](IntermediateNormSurjectivityStatement.md).
It covers arbitrary fields `K L : Type u`, with `Algebra K L` and
`FiniteDimensional K L`. Assuming surjectivity of `N_{L/E}` for every
`E : IntermediateField K L`, it proves, in the target's order, surjectivity of
`N_{L/K}`, every `N_{E/K}`, every `N_{E/F}` for
`F : IntermediateField K E`, and every `N_{L/F}` for
`F : IntermediateField E L`.

All norms are the existing `Langlands.LocalClassField.normUnits`, namely
`Units.map (Algebra.norm _)`. The units are full field units. No separability,
Galois, local-field, characteristic, or cohomological hypothesis is added.
The statement pair and its imported pairs are unchanged.

## Implemented proof

Two private lemmas establish the operations used in the proof.

* `norm_surjective_of_base_equiv` transports norm surjectivity between base
  fields `A` and `B` embedded in a common field `C`. Its ring equivalence
  `e : A ≃+* B` is assumed to commute with the embeddings in `C`. For a unit
  `x : Aˣ`, surjectivity over `B` provides a unit `y : Cˣ` whose norm is the
  image of `x` under `Units.map e.toMonoidHom`. The identity
  `Algebra.norm_eq_of_ringEquiv` then identifies the image under `e` of
  `N_{C/A}(y)` with that same element. Injectivity of `e` and extensionality
  of units give `N_{C/A}(y) = x`.
* `norm_surjective_lower` descends surjectivity in a finite tower
  `A → B → C`. Choose `y : Cˣ` with `N_{C/A}(y) = x`. Then
  `N_{C/B}(y) : Bˣ` maps to `x` by `Algebra.norm_norm`. The Lean proof applies
  that element-level identity after reducing equality of units to equality
  of their underlying field elements.

For the first clause, apply the hypothesis at the bottom intermediate field.
The base equivalence is `(IntermediateField.botEquiv K L).symm`, from `K`
to the bottom field. Its embedding compatibility is discharged by simplification.
The first helper yields surjectivity of `N_{L/K}`.

For the second clause, install `FiniteDimensional.left K E L` and
`FiniteDimensional.right K E L`, and apply the tower helper to `K → E → L`
using the first clause.

For the third clause, let `F : IntermediateField K E`. The canonical subtype
structures supply the algebra maps and scalar towers through `F`, `E`, and `L`.
The proof installs finite-dimensionality of `E/K`, `E/F`, `L/E`, `L/F`, and
`L/(IntermediateField.lift F)` using `FiniteDimensional.left` and
`FiniteDimensional.right`. The hypothesis gives norm surjectivity over
`IntermediateField.lift F`, the image of `F` inside `L`. The equivalence
`IntermediateField.liftAlgEquiv F` identifies `F` with that image, and its
compatibility with the two inclusions into `L` is definitional. The base
transport helper gives surjectivity of `N_{L/F}`, and the tower helper for
`F → E → L` gives surjectivity of `N_{E/F}`.

For the fourth clause, the proof is `hn (F.restrictScalars K)`.
Restriction of scalars leaves the carrier, field structure, and inclusion of
`F` into `L` unchanged. The target explicitly uses the finite-dimensional
instance `FiniteDimensional.right K (F.restrictScalars K) L`, so the hypothesis
at that intermediate field has the required type directly. This is the step
adapted from Worker 68's helper.

## Provenance and scope

This is an internal derived finite-extension argument, not a quotation from a
separate literature result. It combines the published determinant norm
construction in [Norms](Norms.md) with Mathlib's
`Algebra.norm_eq_of_ringEquiv`, `Algebra.norm_norm`, `IntermediateField.botEquiv`,
`IntermediateField.liftAlgEquiv`, and restriction of scalars. It proves the
norm-inheritance prerequisite only; the finite p-group and cyclic-cohomology
arguments remain in their separate modules.
