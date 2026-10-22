# Absolute Hilbert 90 for characteristic-zero fields

`Langlands.ClassFieldTheory.Local.absoluteH1Vanishing` proves exactly
`AbsoluteH1Vanishing.{u}` from `AbsoluteH1Statement`. Thus for every
field `K : Type u` with `CharZero K`, the actual continuous cohomology
`absoluteCohomology K 1` is a subsingleton. The field universe is arbitrary.
The coefficients remain the discrete algebraic-closure units, in additive
notation, over `IntegerScalars.{u} = ULift.{u} ℤ`.

The helper `finiteStageUnitH1_subsingleton` works for a Galois extension
`L/K`, with independent field universes, and an open normal subgroup `N`
of `Gal(L/K)`. It regards `N` as a closed normal subgroup `H` and takes
the intermediate field `E = IntermediateField.fixedField H.toSubgroup`.
The infinite Galois correspondence identifies `E.fixingSubgroup` with
`H`; since this subgroup is open, `E` is finite-dimensional over `K`.
The imported `finiteRelativeH1Vanishing` gives a subsingleton relative H¹
for `E/K`. The explicit `fixedFieldCohomologyIso` identifies the finite
quotient stage with that relative cohomology, so injectivity of its
linear equivalence proves the helper.

For the main theorem, characteristic zero supplies the Galois property
of `AlgebraicClosure K / K`. The proof exposes the existing compactness
instance through `Field.absoluteGaloisGroup` and packages `absoluteUnits K`
as a `DiscreteModule`, using `continuous_unitAction` for joint continuity.
The helper makes every degree-one finite quotient stage a subsingleton.
The categorical colimit universal property then shows that the identity
of `finiteQuotientCohomology A.toRep 1` is zero: its composites with all
colimit inclusions equal zero because their source modules are zero.
The colimit is therefore a zero object and has a subsingleton carrier.
Injectivity of the inverse of `finiteQuotientComparisonLinearEquiv A 1`
transfers that conclusion to the actual continuous cohomology.

This is an internal derived result combining the project's finite-relative
Hilbert 90 theorem, explicit fixed-field coefficient equivalence, and
continuous finite-quotient comparison. Its proof assumes no vanishing or
comparison premise. The imported statement and coefficient definitions
are unchanged. It proves only the absolute H¹ assertion; no H² assertion
is part of this module.

Worker 80 authored the Lean specialization, reused unchanged from host
draft revision 3. Worker 54 prepared this proof pair for the exact published
target and rewrote its documentation to describe the implemented argument.
Worker 22 authored the imported finite-quotient comparison, and Worker 42
authored the closure coefficient continuity construction; their attribution
from the reused draft is retained. The finite-relative Hilbert 90 proof is
the published work of Workers 80 and 66.
