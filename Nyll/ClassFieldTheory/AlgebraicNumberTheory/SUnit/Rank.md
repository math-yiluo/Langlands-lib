# Torsion and rank of the S-unit group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and S a finite set of finite places of K. This file finds the torsion of the S-unit group `SUnitGroup S` and its rank: the unit rank plus #S. Equivalently, the rank is (number of infinite places) + #S − 1. The group itself is defined in an imported file.

## Units and torsion

- `emptyEquivNumberFieldUnits`: the units for the empty set of places are (𝓞 K)ˣ. `fromNumberFieldUnits S` is the resulting injective homomorphism (𝓞 K)ˣ → `SUnitGroup S`.
- `torsion_eq_rootsOfUnity_range`: the torsion of `SUnitGroup S` is the image of the roots of unity `NumberField.Units.torsion K`.

## The divisor map

- `divisorCoordinate S x v`: the exponent of v ∈ S in the principal fractional ideal of x. `valuation_eq_exp_neg_count` says that the valuation of x at v is `WithZero.exp` of minus this exponent. The coordinate is 0 exactly when the valuation is 1, and it is additive in x.
- `divisor` and `divisorLinearMap`: the additive map from S-units to ℤ^S.
- `range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap`: the kernel of the divisor map is exactly the image of the global units.
- `primeIdealPower_classNumber_isPrincipal`: for v ∈ S, the prime raised to the class number h_K is principal. A generator is an S-unit with divisor h_K times the basis vector at v.

## Rank

- `finrank_divisor_range`: the image of the divisor map has rank #S.
- `moduleFinite`: the S-unit group is finitely generated.
- `finrank_divisor_ker`: the kernel has the unit rank `NumberField.Units.rank K`.
- `finrank`: `Module.finrank ℤ (Additive (SUnitGroup S)) = NumberField.Units.rank K + S.card`.
- `finrank_modTorsion` and `finrank_modTorsion_eq_card_infinitePlaces_add_card_sub_one`: the same rank for the S-units modulo torsion, also written as (number of infinite places) + #S − 1.

## Proof

The divisor map has the global units as kernel. Mathlib's Dirichlet unit theorem (`NumberField.Units.finrank_eq`) gives the kernel's rank. The image lies in ℤ^S and contains the #S independent vectors h_K·e_v, which exist because the class group is finite. Rank additivity along the divisor map then gives the formula. Finite generation follows the same way: the image is a submodule of ℤ^S, and the kernel is the image of the finitely generated unit group.

## Points to watch

- S contains only finite places. The infinite places are always implicit, as in the usual formula with #S counting them.
- The rank is `Module.finrank ℤ` of the additive group, that is, the rank of its free part.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/Rank.lean`: the Lean file is the source byte for byte (SHA-256 `74c409144f67159db0b9c10b7ec7adb707d75b6fbf03a19f7784265475bbbcfa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
