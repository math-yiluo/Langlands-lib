# Relative unit filtrations and literal residue coordinates

Author: Worker 27.

This is a derived algebraic construction using the published
`Langlands.LocalField.RelativeIntegers` and
`Langlands.ClassFieldTheory.Local.GradedUnitCoordinates`. It extends their
actual maps and coordinate definitions; it makes no additional claim of
formalizing an original literature passage. Imported constructions retain
their original authorship.

All declarations are in `Langlands.PadicField.TopologicalData`. For a prime
`p`, the source and target are arbitrary `PadicField.{u} p` and
`PadicField.{v} p`, with independent universes, supplied realizations `T` and
`S`, and an actual `Algebra F.Carrier E.Carrier` compatible with the p-adic
base by `IsScalarTower (Padic p) F.Carrier E.Carrier`.

The proved localness of `relativeIntegerMap T S` sends the source maximal
ideal into the target maximal ideal. `relativeIntegerMap_mem_maximalIdeal_pow`
uses the image of an ideal power and monotonicity of powers to preserve
membership in every natural power. The case zero is included.
`relativeIntegerMap_mem_congruenceUnits` applies this to the difference
between an integer unit and one, using the published congruence-membership
criterion.

`relative_mem_unitFiltration` maps an integer-unit witness to the corresponding
target witness. `relativeUnitFiltrationMap T S n` bundles this restriction of
the given field embedding as a homomorphism between the existing level `n`
filtration groups. Its computation rules expose exactly `Units.map` of the
given field algebra map and the underlying field value.

`filtrationIntegerUnit_relativeUnitFiltrationMap` proves that recovering the
unique integer unit after mapping a filtration unit gives the image of the
source recovered integer unit. Equality is checked on field values using
`filtrationIntegerUnit_coe`. At level zero,
`zeroUnitCoordinate_relativeUnitFiltrationMap` then identifies reduction with
`Units.map` of the existing `relativeResidueMap T S`. No uniformizer is needed
for any of these declarations.

For the remaining declarations, choose any source element `π` with
`T.ord π = 1`, and assume explicitly that its actual image also has target
order one. `unitCoefficient_relativeUnitFiltrationMap` identifies the target
integer coefficient with the image of the source integer coefficient.
The proof checks the two integer subtypes on field values and uses
preservation of subtraction, division, powers and one. These are the literal
quotients `(x - 1) / π^n`; there is no selection of a coefficient from its
residue or from an equality of functions on a finite field.

`residue_unitCoefficient_relativeUnitFiltrationMap` reduces that integer
identity using `relativeResidueMap_residue`.
`positiveUnitCoordinate_relativeUnitFiltrationMap` expresses the same result
for the existing positive-level coordinate homomorphisms, with `0 < n` and
`Multiplicative.ofAdd` applied to the actual residue-field image. The integer
coefficient and its residue identity hold also at `n = 0`; only the additive
coordinate requires positivity. At the identity unit the literal numerator
is zero and all identities still hold.

The uniformizer image order condition is an explicit hypothesis, not a
consequence of arbitrary field extension. The module assumes no finiteness,
Galoisness or unramifiedness. It proves filtration preservation and these
coordinate identities; norm formulas, ramification break preservation and the
prime-degree base-change norm theorem require separate arithmetic proofs.

The Mathlib ingredients are `IsLocalRing.map_maximalIdeal_le`,
`Ideal.mem_map_of_mem`, `Ideal.map_pow`, monotonicity of powers, and extensionality
for units and subtypes. No new axioms or proof holes are introduced.
