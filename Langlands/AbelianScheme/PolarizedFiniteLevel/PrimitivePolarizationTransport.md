# Transport of primitive polarization factors along isomorphisms

This internal module compares primitive factors of polarizations along
isomorphisms of abelian schemes. It uses the published transport of maps to
the constructed dual, `DualWitness.transportMap`, from
`PolarizationIsoTransport`. It adds no literature assertion. The positivity
of polarization ratios enters only as the explicit hypothesis
`PolarizationRayPositivityStatement`, a separate statement target in the module
`PolarizationRayPositivityStatement`.

## Transport as an additive equivalence

`DualWitness.transportMap P e WA WB lam` is `e.hom ≫ lam ≫ WA.map P WB e.hom`
for an isomorphism `e : A ≅ B` and dual witnesses `WA`, `WB`.
`transportMap_nsmul` and `transportMap_zsmul` prove additivity in `lam` for
natural and integer multiples, by bilinearity of composition.
`transportMap_symm_transportMap` shows that transporting back along `e.symm`
recovers `lam`. This uses contravariant functoriality of the published dual
maps (`DualWitness.map_comp`, `DualWitness.map_id`).

`DualWitness.transportAddEquiv` is the definition of the module. It is the
additive equivalence from maps `B ⟶ WB.dual P` to maps `A ⟶ WA.dual P` given
by transport along `e`, with inverse given by transport along `e.symm`.
`transportAddEquiv_apply` unfolds it.

`isPrimitiveHom_transportMap` shows that transport preserves primitivity
(`Tate.IsPrimitiveHom`). If `j • g` is the transport of `lam`, then
transporting `g` back gives a map whose `j`-th multiple is `lam`.

## Equality of primitive factors

`transportMap_eq_of_primitive` assumes `PolarizationRayPositivityStatement`.
It also takes the finite-étale torsion statement, a connected locally
noetherian base with every positive integer a unit, an algebraically closed
point `s`, and relative dimension `g > 0` for `A`. Let `lamA` and `lamB` be
polarizations with `lamA = kA • mA` and `lamB = kB • mB`, where `mA`, `mB` are
primitive and `kA`, `kB > 0`. Suppose `a • transport(lamB) = b • lamA` with
integers `a ≠ 0` and `b`. Then `transport(mB) = mA`.

The transport of `lamB` is a polarization (`isPolarization_transportMap`),
so the positivity hypothesis, applied at the nonempty base given by `s`,
yields `a b > 0`. Additivity rewrites the equation as
`(a kB) • transport(mB) = (b kA) • mA`. Both integer coefficients are nonzero
with the same sign. Multiplying by that sign gives an equation between
positive natural multiples. The uniqueness theorem
`Tate.eq_of_nsmul_eq_nsmul_of_isPrimitiveHom` of the bundled `PrimitiveHom` module concludes, since both
`transport(mB)` and `mA` are primitive.

This module does not prove `PolarizationRayPositivityStatement`, show that a
primitive factor is a polarization, or compute degrees.
