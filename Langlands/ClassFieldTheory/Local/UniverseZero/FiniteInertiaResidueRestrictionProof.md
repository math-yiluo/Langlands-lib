# Supplied residue actions commute with finite inertia restriction

The proof follows the representative argument described below. The theorem proves
`Langlands.LocalClassField.UniverseZero.FiniteInertiaResidueRestrictionStatement.{u, v}`
as `Langlands.LocalClassField.UniverseZero.finiteInertiaResidueRestriction`.
The universes `u` and `v` are independent. All three supplied realizations
`TF`, `TU`, and `TE` remain arbitrary, and the proof uses the actual maps
and actions named in the published statement.

This is an internal consequence of the published finite inertia constructions
and the supplied integer and residue maps. Its provenance is the defining
pair `Langlands/ClassFieldTheory/Local/UniverseZero/FiniteInertiaField` and the target
pair `Langlands/ClassFieldTheory/Local/UniverseZero/RamifiedResidueStatement`; it does
not require an additional arithmetic theorem.

For a residue element `y` of the inertia fixed field, the proof chooses an
integral representative `z` using `IsLocalRing.residue_surjective`. The
definitions of the supplied residue actions and
`PadicField.TopologicalData.relativeResidueMap_residue` rewrite both sides as
the residue in `TE` of integer elements. Applying `congrArg TE.residue` and
`Subtype.ext` reduces their equality to equality in `E.Carrier`. The coercion
of the relative integer map is the actual field inclusion, and the coercion
of each integer automorphism is its actual field automorphism. Consequently
the remaining equality is exactly `finiteInertiaRestriction_apply`.

The tower certificate `finiteInertiaPadicTower` and the Galois certificate
`finiteInertiaField_isGalois` are installed locally. The published target
pair and its import closure are unchanged.
