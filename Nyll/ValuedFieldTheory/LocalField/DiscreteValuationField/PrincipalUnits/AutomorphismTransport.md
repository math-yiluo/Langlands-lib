# Field automorphisms acting on units and principal units

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a field `K` with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, maximal ideal 𝔪 and higher principal unit groups U^n = 1 + 𝔪^n for n ≥ 1 and U^0 = O^*. Throughout, `e : K ≃+* K` is a field automorphism with O preserved in the sense `hmem`: x ∈ O ↔ e x ∈ O for every x. The file transports `e` to O, to the residue field, to O^* and to every quotient O^*/U^n, and shows that if `e` acts trivially on the residue field then it acts trivially on O^*/U¹.

## Main definitions and results

- `valuationSubringRingEquivOfPreserves`: the restriction of `e` to a ring automorphism of O. It preserves each power 𝔪^n (`..._mem_maximalIdeal_pow_iff`).
- `valuationSubringResidueFieldEquivOfPreserves`: the induced automorphism of the residue field, with `..._apply_residue` relating it to the residue map.
- `valuationSubringUnitEquivOfPreserves`: the induced automorphism of O^*; `residueUnitHom_valuationSubringUnitEquivOfPreserves` makes it compatible with reduction to residue-field units.
- `valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff` and `higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves`: the automorphism of O^* maps each U^n onto itself.
- `unitsModPrincipalUnitEquivOfPreserves F e hmem n`: the induced automorphism of O^*/U^n.
- `unitEquiv_div_mem_principalUnit_one_of_residueUnitHom_fixed` and `..._of_residueFieldEquiv_fixed`: if `e` fixes residue classes of units (respectively, the residue field pointwise), then e(u)/u ∈ U¹ for every unit u; the `..._mod_principalUnit_one_eq_...` forms state the same in O^*/U¹.
- `unitsModPrincipalUnitEquivOfPreserves_one_eq_refl_of_residueFieldEquiv_fixed`: under the residue-field hypothesis, the induced automorphism of O^*/U¹ is the identity.

## Proofs

Preservation of 𝔪^n follows from the fact that a ring automorphism of a local ring maps the maximal ideal onto itself. The triviality results use that U¹ is the kernel of reduction O^* → (residue field)^*.

## Points to note

- Preservation of O is a hypothesis, not deduced from `e`; no continuity or uniqueness of the valuation is used.
- The triviality statement concerns only level 1; nothing is said about the action on U^n/U^(n+1) for n ≥ 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/AutomorphismTransport.lean`: the Lean file is the source byte for byte (SHA-256 `af40ca6895ae89f4626f562cbe3c0b1664a6dc930d78e844f9f8ebd2ee162403`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
