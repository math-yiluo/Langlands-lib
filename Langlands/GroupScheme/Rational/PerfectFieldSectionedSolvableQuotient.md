# Actual split geometric radicals and sectioned solvable torus quotients

Worker 1556.

`SplitGeometricUnipotentRadical` stores an actual group scheme, its inclusion,
the existing ground-field and algebraic-closure radical predicates, and a finite
represented split series. `perfectFieldSplitGeometricUnipotentRadical`
constructs this data for every smooth connected affine group scheme over a
perfect field in an arbitrary universe. It requires no solvability hypothesis.

The construction applies the published `unipotentRadicalExistence` proof to the
base change to the algebraic closure. Perfectness makes this extension Galois,
so `IsUnipotentRadical.galoisRadicalDescent` supplies a ground-field radical and
an actual source isomorphism recovering the chosen geometric inclusion.
Transport through this isomorphism proves that the descended inclusion satisfies
`LeviSubgroup.IsGeometricUnipotentRadical`. Its source is smooth and connected
by the radical predicate and affine as a closed subgroup of the affine ambient
group. The published `perfectFieldUnipotentSplit` proof supplies the finite
split series.

`SplitGeometricRadicalSectionedTorusQuotient` retains a sectioned torus quotient
of that same inclusion. For a solvable group over a perfect field,
`perfectFieldSectionedSolvableTorusQuotient` constructs this data by the existing
`LeviSubgroup.IsGeometricUnipotentRadical.sectionedTorusQuotient` assembly. The
absolute `SolvableTorusQuotientStatement` and
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement` remain explicit
premises. The construction discharges radical existence and perfect-field
splitness with proofs; it does not claim to discharge the two remaining
premises or prove finite-field envelope normality.

The `torus` accessor views the original quotient as a commutative group scheme
using `IsTorus.isCommMonObj`. It changes neither the quotient object nor its
projection, full fppf kernel, or homomorphic section. All radical and kernel
identities retain the existing subgroup-functor meaning on every relative test
scheme, including nonreduced tests.

This is an internal composition of the imported Library constructions in
`Reductive.GaloisRadicalDescent`, `Unipotent.PerfectFieldSplitProof`, and
`Rational.SolvableMaximalTorusAssembly`; it introduces no additional external
mathematical assertion.
