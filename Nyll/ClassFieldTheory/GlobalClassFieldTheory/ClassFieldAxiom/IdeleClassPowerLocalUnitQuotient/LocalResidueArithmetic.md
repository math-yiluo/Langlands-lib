# Residue fields, ramification and ideal norms at finite places

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file relates the absolute norm of a prime of a number field to the residue field and the ramification invariants of the completion, and proves the relation `[E : ℚ_p] = e · f` for a mixed-characteristic local field E. These identities feed the computation of local power indices at finite places.

## Main results

- `absNorm_eq_card_adicResidueField`: for a finite place v of a number field K, `N(v)` equals the cardinality of the residue field of `K_v`.
- `ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex`: for a field E with a complete discrete valuation ν into `ℤₘ₀` that is surjective, with finite residue field and characteristic zero, the ramification index read off from `ν(p)` agrees with the ramification index of E over `ℚ_p` as an extension of discretely valued fields.
- `card_localField_residueField_eq_pow_residueDegree`: under the same hypotheses (surjectivity not needed), the residue field of E has `p^f` elements, f the residue degree over `ℚ_p`.
- `finrank_qp_eq_ramificationIndex_mul_residueDegree`: `[E : ℚ_p] = e · f`.
- `absNorm_eq_residueCharacteristic_pow_residueDegree`: `N(v) = p^f` for the completion `K_v`.

## Proof

The ramification comparison writes the image of p in E as a unit times a power of a uniformizer of E; `e · f` comes from the imported degree formula for finite separable extensions of complete discretely valued fields.

## Points to watch

- Two ramification indices coexist in the library: one defined from the valuation of p (`ramificationIndexOfWithZeroValuation`) and one for extensions of discretely valued fields; the second lemma states that they agree.
- The structure of E as a local field over `ℚ_p` (residue characteristic, `ℚ_p`-algebra structure) is the library's own construction from ν, through `ofWithZeroValuation` and `mixedQPadicContext`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/LocalResidueArithmetic.lean`: the Lean file is the source byte for byte (SHA-256 `858d6ff668be7d860d5fa65e83d175fc528ca72e0bd28740cdfd926121dfc0bf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
