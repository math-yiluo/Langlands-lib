# The subgroups `dℤ` of the integers and their cyclic quotients

Module `Nyll.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines, inside the integers written multiplicatively (`Multiplicative ℤ`, the shape of a discrete value group), the subgroup of multiples of a fixed integer `d`, and identifies the quotient with `ℤ/|d|`. It is pure group theory with no valued-field hypotheses, though its declarations sit in the namespace `LocalFieldTheory.DiscreteValuationField`.

## Definitions and results

- `integerMultipleSubgroup d`: the elements of `Multiplicative ℤ` whose underlying integer is divisible by `d`. Membership lemmas `mem_integerMultipleSubgroup_iff` and `ofAdd_mem_integerMultipleSubgroup_iff` say exactly that; `ofAdd_mul_mem_integerMultipleSubgroup` and its commuted form put `d·n` in it.
- `integerMultipleSubgroup_le_of_dvd`: if `a ∣ b` then `bℤ ≤ aℤ`.
- `integerMultipleSubgroup_one_eq_top`: `1ℤ` is everything.
- `multiplicativeIntToZModHom d`: reduction `Multiplicative ℤ →* Multiplicative (ZMod |d|)`; it is surjective, with kernel `integerMultipleSubgroup d`.
- `valueModIntegerMultipleSubgroupEquivZMod d`: the isomorphism `Multiplicative ℤ ⧸ dℤ ≃* Multiplicative (ZMod |d|)`, sending the class of `n` to `n mod |d|` (`valueModIntegerMultipleSubgroupEquivZMod_mk`).

## Watch for

- The modulus is `d.natAbs`, so negative `d` gives the same quotient as `|d|`, and `d = 0` gives `ZMod 0 = ℤ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/GroupTheory/IntegerMultipleSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `5c87eec1ebbb9bf70af3b085c28111cc31e9e65a10643431b8d3fdbfb62c4efa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
