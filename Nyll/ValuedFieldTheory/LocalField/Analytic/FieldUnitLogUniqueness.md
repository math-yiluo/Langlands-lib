# Homomorphisms from local-field units to torsion-free groups

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogUniqueness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` with finite residue field of `q` elements, the file shows that a homomorphism from `Kˣ` to a torsion-free additive group is determined by its values on the first principal units and on one uniformizer. This is the uniqueness step for logarithms on `Kˣ`.

- `residueField_card_sub_one_ne_zero`: `q − 1 ≠ 0`.
- `residueRootsOfUnity_fieldUnitHom_pow_card_sub_one_eq_one`: the image in `Kˣ` of a residue root of unity (Teichmüller factor) has order dividing `q − 1`.
- `monoidHom_toMultiplicative_residueRoot_eq_one`: every homomorphism from `Kˣ` to a torsion-free additive group kills these roots of unity.
- `monoidHom_toMultiplicative_ext_of_agree_principalUnits_and_uniformizer`: two such homomorphisms that agree on the principal units and on a uniformizer `ϖ` are equal. Here `ϖ` is a uniformizer for a multiplicative integer valuation `V` on `Kˣ` whose units are exactly the units of the valuation ring.

The proof writes each unit as a root of unity times a principal unit times a power of `ϖ`. The target group is written `Multiplicative A`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/FieldUnitLogUniqueness.lean`: the Lean file is the source byte for byte (SHA-256 `bb2b94ef04080279b1d9db91990c315e36b6227327064b6989e1d6cb0c8b79fa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
