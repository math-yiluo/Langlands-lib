# Existence of actual unitary cuspidal contragredients

Module: `Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof`. Declaration:
`Langlands.Automorphic.cuspidalUnitaryContragredientExistence :
CuspidalUnitaryContragredientExistenceStatement.{uF}`.

This proves the Library statement `CuspidalUnitaryContragredientExistenceStatement`
(module `Langlands.Automorphic.CuspidalContragredientStatement`): every actual cuspidal
operator realization `T` of rank `r + 1` over a number field `F` with compact adele quotient and
with unitary central character has an actual cuspidal operator realization `T'` that is a
full-operator contragredient of `T` (`IsContragredientOf`) and again has unitary central
character.

## Implemented proof

The theorem is `contragredientExistence_of_siegelFiniteness` (module
`CuspidalAdmissible.JointAdmissibility`) applied to `siegelSetGLFiniteness` (module
`Langlands.Global.AdelicGLSiegelFinitenessProof`). The route:

1. **Contragredient from joint admissibility** (`ContragredientAssembly`): the conjugate
   realization `T.conjugate`, paired with `T` by a unitary form, is a contragredient as soon as
   `T` is jointly admissible (Library `isContragredientOf_of_unitaryForm`); it has unitary
   central character.
2. **Joint admissibility from separation** (`AdmissibilityReduction`, with the Casimir and
   compact Casimir annihilators of `CasimirAnnihilator`, `CompactCasimirAnnihilator` and the
   energy bound of `EnergyBound`): vectors in the image of a multiplicity space satisfy one
   energy bound, so it suffices that finitely many functionals separate the `L`-invariant
   vectors with `energy ≤ C · b(e, e)`.
3. **Separation for the band unitary form** (`Separation`, using `EnergyConversion`, `Split`,
   `CuspRealization`, `CompactEstimate`, `CompactUnfold`, `Unfolding`, `BandShift` and their
   helpers): the band integral of `|e|²` is bounded by its integral over a Siegel set over the
   band; on the cusp regions the vanishing constant terms give an exponentially small multiple
   of the derivatives' band integrals (multiplicity of Siegel sets bounded by Siegel
   finiteness), and on the compact region local averages over small exponential boxes control
   `e` up to a small multiple of the derivatives; derivatives are controlled by the energy.
4. **Siegel finiteness** (`AdelicGLSiegelFinitenessProof`): proved by heights along torus
   elements, comparability of torus coordinates, and unitarity of the compact factor.
