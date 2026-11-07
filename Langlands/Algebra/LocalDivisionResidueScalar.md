# Base residue scalars and a generator lift

Let `K` be a nonarchimedean local field with its supplied valuative relation and
compatible topology, and let `D` be a finite-dimensional central division
`K`-algebra. The carriers have the same arbitrary universe `u`, and the
characteristic is unrestricted. Write

```
v = localReducedNormValuation K D,
R = DivisionValuation.Residue v.
```

The type `R` is the actual quotient of the integer subring by its strict-value
ideal. Throughout this module, the field structure on `R` is the one constructed
by `localDivisionResidueField K D`; it extends the original quotient operations.
The notations `𝒪[K]` and `𝓀[K]` denote the integer subring and its residue field
for the original base-field valuation.

## Constructions

In namespace `Langlands.CentralDivision`,
`localDivisionIntegerMap K D` is the ring homomorphism

```
𝒪[K] →+* v.integer
```

whose underlying function is the original scalar inclusion `algebraMap K D`.
The theorem `localDivisionIntegerMap_coe` records this equality. Composing this
map with actual quotient reduction defines `localDivisionBaseReduction K D`.
Its kernel is characterized exactly by

```
localDivisionBaseReduction K D a = 0 ↔ valuation K (a : K) < 1.
```

The instance `localDivisionBaseReduction_isLocalHom` proves that this
homomorphism is local: if an integral scalar reduces to a unit, it was already
a unit of the original integer subring.

The map `localDivisionResidueScalarMap K D` descends this homomorphism to a
field embedding

```
𝓀[K] →+* R.
```

Its value on the residue of every original integral scalar is the reduction of
that scalar's original image in `D`, as stated by
`localDivisionResidueScalarMap_residue`. The theorem
`localDivisionResidueScalarMap_injective` proves injectivity.
The explicit instance-reducible definition `localDivisionResidueAlgebra K D`
equips `R` with precisely this `𝓀[K]`-algebra structure.
Under that structure, `localDivisionResidue_finiteDimensional` proves
`FiniteDimensional 𝓀[K] R`. It uses the already established finiteness of the
actual residue carrier; it does not compute its extension degree.

The theorem `exists_localDivisionResidue_unit_generator` gives a unit
`a : v.integerˣ` such that for each `z : Rˣ` there exists `n : ℕ` with

```
z = Units.map (DivisionValuation.reduction v).toMonoidHom (a ^ n).
```

Its consequence `exists_localDivisionResidue_generator` gives an integral
unit `a` such that every `z : R` is zero or, for some natural number `n`,

```
z = DivisionValuation.reduction v (a.val ^ n).
```

These are existence statements about an actual original integral unit and its
reduction, rather than a generator of a separately chosen model of the residue.

## Implemented proofs and internal provenance

These are internal consequences of the imported canonical valuation,
finite-residue and unit-lifting results, together with Mathlib's residue-field
universal property and cyclicity of finite field unit groups. No external
structural premise is added.

The scalar restriction of `v` is the original valuation raised to the positive
reduced degree. A scalar of value at most one therefore maps to an integer.
The quotient's exact strict-value kernel and cancellation of this positive
power prove the scalar-reduction kernel test. If a scalar reduction is a unit,
it is nonzero. The test rules out value less than one; combined with integrality,
this forces value exactly one. The integral-element unit criterion now proves
the local-homomorphism instance.

Mathlib's `IsLocalRing.ResidueField.lift` descends the local homomorphism to
the original residue field. The compatibility formula holds by definition;
injectivity follows because a unital homomorphism from a field is injective.
The resulting algebra is constructed directly from this ring homomorphism.
Finiteness of `R` supplies finite dimensionality over the embedded base field.

Mathlib's cyclicity theorem supplies a generator `g` of the finite group `Rˣ`.
The imported `DivisionValuation.reduction_units_surjective` lifts `g` to a unit
`a` of the actual integer subring. In a finite group, membership in the integer
powers of `g` is equivalent to membership in its natural powers. Applying this
to each unit and using reduction's power law proves the unit-generator
statement. Finally, a nonzero field element defines a unit, and taking its
underlying value proves the zero-or-power statement.

## Scope

This module identifies the actual base residue embedding and the resulting
finite-dimensional residue-field extension, and lifts a multiplicative generator
to an original integral unit. It does not compute the residue degree, choose a
Henselian or unramified lift, construct an unramified cyclic maximal subfield,
or prove local SK1 or the local Kneser–Tits theorem.
