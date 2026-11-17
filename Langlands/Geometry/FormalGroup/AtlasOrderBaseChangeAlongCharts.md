# Actual rational chart maps through supplied-target coefficient extension

This internal unit states actual chart formulas for full-order quasi-isogeny
extension to supplied target scalar structures. It combines the existing raw
coefficient-extension formula with scalar equality transport of actual global
formal order maps and tensors. It makes no new literature assertion.

The atlas `QuasiIsogeny.reAlgebra` construction retains both actual rational
maps and their inverse equations under equality of scalar structures; its
forward projection is the existing full-order rational Hom transport.

`baseChangeReAlgebraOrderChartIso` compares a test chart of the scalar-retyped
extended atlas with the original selected chart, transported to the same
scalar structure on the test ring. `coefficientAlgebra_comp_transport` supplies
exactly that equality on the test ring. The source-chart version retains the
original source selected through the target image generator and the original
cover equality. Both constructions eliminate the scalar equality and retain
the existing actual raw coefficient chart isomorphisms.

`originalChartReAlgebra` transports the specified original chart quasi-isogeny
to the induced new scalar structure on the same test ring. It eliminates the
base scalar equality and retains the original chart map at reflexivity.
The result explicitly fixes the new scalar structure on the test ring.
`onChart_baseChangeReAlgebra` expresses the extended actual chart quasi-isogeny
as the source comparison, this transported original chart map, and the inverse
target comparison. Its proof eliminates the scalar
equality and applies the existing complete raw chart formula. The two
`baseChangeAlong` chart isomorphisms specialize this to the supplied algebra
map. `onChart_baseChangeAlong` identifies the specified supplied-target
quasi-isogeny with the scalar transport of raw extension by its exact forward
map, then applies that formula. Equality is of complete actual quasi-isogenies,
including their inverse maps; no formal-map equality is deduced from points.

The parameters are arbitrary commutative rings `O`, `R`, `S`, an acting ring `D`
over `O`, a field `F` over `O`, finite coordinate types and actual atlas order
actions with equal covers. Coefficient rings and tests share universe `v`,
while `O`, `D` and `F` may have separate universes. Quasi-isogenies retain the
existing domain/fraction-field assumptions. Covers may be infinite and scalar
maps may merge generators. Compatibility of framed Nilp-base extension with
framed comparisons remains a further construction.
