# Topological transport of adeles, ideles and idele classes

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields K and M with a ℚ-algebra isomorphism e : K ≃ M, this file upgrades the library's algebraic transports of adeles, ideles and idele classes to multiplicative homeomorphisms, which for ideles and idele classes are isomorphisms of topological groups.

- `adeleCongr_symm`: the inverse of `adeleCongr e` is `adeleCongr e⁻¹`.
- `adeleCongrContinuousMulEquiv e`: `adeleCongr e` as a multiplicative homeomorphism of the adele rings (`≃ₜ*`); continuity in both directions comes from `continuous_adeleCongr`.
- `ideleCongrContinuousMulEquiv e`: the induced isomorphism of topological groups `IdeleGroup K ≃ IdeleGroup M`, through the identification of ideles with adele units (`IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv`); `..._apply` says its underlying map is `ideleCongr e`.
- `ideleClassCongrContinuousMulEquiv e`: the isomorphism of topological groups of idele class groups, with underlying map `ideleClassCongr e` (`..._apply`); continuity follows from the quotient topology.

The step from adeles to ideles relies on `IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv`, defined in another file, which matches the idele topology with the topology of the units of the adele ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivIdeleClassTopology.lean`: the Lean file is the source byte for byte (SHA-256 `393153c9796c63274004b7743e35cf40332f5add452ee9b01e4df57991af119b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
