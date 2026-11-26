# The outer type A Hasse kernel from the unitary presentation and arithmetic

Module: `Langlands.GroupScheme.Rational.NumberFieldOuterTypeAHasseReduction`.

`NumberFieldOuterTypeAHasseReductionStatement.{u}` is the implication

```text
OuterTypeAUnitaryAlgebraPresentationStatement →
  NumberFieldLandherrStatement → NumberFieldUnitaryNormStatement →
    NumberFieldOuterTypeAHasseStatement
```

in one universe `u`. The target `NumberFieldOuterTypeAHasseStatement` is the Hasse
kernel for simply connected absolutely almost-simple groups of outer type `A_n`
over number fields, stated in `Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction`.
The three premises are stated in
`Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraPresentationStatement`,
`Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement` and
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormStatement`; this module does
not prove them.

`numberFieldOuterTypeAHasse_of_unitaryPresentation` proves the implication, and
`numberFieldOuterTypeAHasseReduction` restates it as a proof of the reduction
statement. Given `G`, its index data and numbering, and a locally trivial cocycle on
a finite Galois field cover, the presentation premise supplies a separable quadratic
extension `E/F`, a central simple `E`-algebra `B` with a unitary involution `τ`, and
a presentation of `G` as `SU(B, τ)`. With `FiniteDimensional F E` from the quadratic
degree and `FiniteDimensional F B` by transitivity,
`UnitaryAlgebra.isTrivial_of_landherr_unitaryNorm` (module
`Langlands.GroupScheme.Rational.NumberFieldUnitaryAlgebraHasse`) trivializes the
cocycle from the two arithmetic premises.

## Provenance

This is an internal reduction following the classical route for groups of type
`²A_n`: Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
Theorem (26.9), identifies the group with `SU(B, τ)`, and Platonov and Rapinchuk,
*Algebraic Groups and Number Theory* (1994), §6.7, pp. 359–360, deduce the Hasse
principle for `SU(B, τ)` from Landherr's theorem (Theorem 6.27) and the unitary norm
theorem (Theorem 6.28); see also Kneser, *Lectures on Galois Cohomology of Classical
Groups* (1969), §5.5.
