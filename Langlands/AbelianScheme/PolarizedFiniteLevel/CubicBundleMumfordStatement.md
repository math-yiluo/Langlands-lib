# The Mumford map of the cubic diagonal bundle

`CubicBundleMumfordStatement` asserts that, for every existing prerequisite
package and every ordinary polarized finite-level datum over a field, the
Mumford map of the actual bundle `a.cubicBundle` is `6 • a.polarization`.
The statement supplies the base inverse, its evaluation, the inverse of the
normalized bundle, and that evaluation as existential conclusions.

This is an internal consequence of the published diagonal identity
`polarizationDiagonalMumford` and multiplicativity of the Mumford construction
on tensor powers. The diagonal bundle has Mumford map `2 • polarization`;
its actual tensor cube therefore has map `6 • polarization`. No restriction
on the characteristic, the level, or the degree is imposed. Algebraic closure
is unnecessary for this identity.

The definition adds no ampleness, finite-cohomology, vanishing, or numerical
degree hypothesis. It asserts the identity of actual morphisms to the datum's
existing dual scheme. It does not assert the cohomology or degree formula.
