# Affineness of linear homogeneous quotients by connected reductive subgroups

`Langlands.GroupScheme.reductiveLinearQuotientAffine` proves
`Langlands.GroupScheme.ReductiveLinearQuotientAffineStatement.{u}` for every
universe `u`. Over any algebraically closed field, an actual connected
reductive group with a closed representation into `GL_(Fin N)` has an affine
structure morphism on each supplied homogeneous quotient `Q`. This applies
in every characteristic and for all natural numbers `N`, including zero.
The conclusion is `IsAffineHom Q.scheme.hom` for the original `Q`, whose exact
right-coset fibers are part of the quotient data on every relative scheme
test, including nonreduced and nonaffine tests.
[Published statement](LinearQuotientAffineStatement.md)

The proof applies `reductiveLinearQuotientAffine_of_geometricReductivity` to
`IndependentHaboush.reductiveGeometricReductivity`. The latter proves the full
geometric-reductivity statement through the rank-one central cover and the
Steinberg big-cell construction. The reduction applies it to the given group
using `IsConnectedReductive.isPseudoReductive`. The affineness argument
constructs affine principal opens whose defining sections generate the unit
ideal in the actual quotient's section ring. It obtains the unit ideal via
invariant polynomials and the section-ring equivalence induced by the
supplied projection. The principal-open criterion gives affineness of `Q`,
and its structure morphism to the affine base is affine.
[Geometric reductivity proof](IndependentGeometricReductivityProof.md)
[Quotient reduction](LinearQuotientAffineOfGeometricReductivity.md)
[Principal-open argument](../HomogeneousQuotientAffineOfGeometricallyReductive.md)

A dependency audit followed the types and values of every declaration
reachable from `reductiveLinearQuotientAffine`, including opaque proof
values. The closure contained zero occurrences of the five excluded
statements, their proofs, the older Haboush proof, and the audited
regular-cocharacter and Borel steps. As a check on the scan, the closure of
the older Haboush proof did reach the excluded `regularCocharacterBorel`.
[Dependency audit method](../../../notes/group-schemes/haboush-independence-audit.md)
