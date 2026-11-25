# The field norm on unit groups

Module `Nyll.ValuedFieldTheory.LocalField.NormUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L / K`, the file defines the norm map `Lˣ → Kˣ` and records two of its basic properties. Nothing here uses a valuation or a topology.

## Main declarations

- `algebraNorm_neg`: `Algebra.norm K (-x) = (-1)^[L:K] · Algebra.norm K x`, where `[L:K]` is `Module.finrank K L`.
- `normUnits K L`: the group homomorphism `Lˣ →* Kˣ` induced by `Algebra.norm K`; `normUnits_apply_coe` says its value, as an element of `K`, is the algebra norm.
- `normUnits_tower`: for a tower `K ⊆ M ⊆ L` with `L` free over `M`, `normUnits K M (normUnits M L x) = normUnits K L x` for `x` in `Lˣ`. It is Mathlib's `Algebra.norm_norm` read on units.

## Watch for

No finiteness of `L / K` is assumed. For an infinite extension `Algebra.norm` is the constant 1 and `finrank` is 0, so the statements hold but carry no information; `normUnits_tower` needs the instance `Module.Free M L`, which holds automatically for fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`: the Lean file is the source byte for byte (SHA-256 `9010c9b5103ae51fa63151ad290a7188e3dd47fc4b4875733dbe41d7076d1a52`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
