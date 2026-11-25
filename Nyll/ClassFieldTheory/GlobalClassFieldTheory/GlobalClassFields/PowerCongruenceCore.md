# Power-congruence subgroups inside finite-index idèle-class subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PowerCongruenceCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index `n` in the idèle class group `C_K` of a number field `K`. Every `n`-th power lies in `H`, and `H` contains a ray congruence subgroup. The file combines the two to show that `H` contains the subgroup of idèle classes represented by idèles that are local `n`-th powers at the infinite places and at a suitable finite set `S`, and integral units elsewhere. The module docstring describes this as the power-congruence step of the existence proof for global class fields.

## Main result

- `ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup`: let `H` be closed of finite index, `n` its index (as an element of `ℕ+`), and `S` a finite set of finite places containing the support of the finite part of `RayClass.modulusInsideClosedFiniteIndex H hclosed`, the library's modulus whose congruence subgroup lies in `H`. Then `ideleClassPowerLocalUnitSubgroup n S ∅ ≤ H`.

## Proof

Take an idèle `a` that is an `n`-th power at every infinite place and at every place of `S`, and a unit elsewhere. Gather the chosen local `n`-th roots into one idèle `b`, equal to `1` at finite places outside `S`. Then `u = a · b⁻ⁿ` is `1` at the infinite places and at `S`, and a unit at the other finite places, where the modulus has exponent `0`. So `u` lies in the idèle congruence subgroup of the modulus, and its class lies in `H`. The class of `bⁿ` lies in `H` because `n` is the index of `H` in an abelian group, so `a = bⁿ · u` maps into `H`.

## Points to watch

- The exponent of the power subgroup is exactly the index of `H`, and only the case with the second set of places of `ideleClassPowerLocalUnitSubgroup` empty is treated.
- `H` must be closed for the modulus `RayClass.modulusInsideClosedFiniteIndex` to be available; the finite index is passed as an instance.
- The local conditions at infinite places are `n`-th powers at every infinite place, not just positivity at real places.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/PowerCongruenceCore.lean`: the Lean file is the source byte for byte (SHA-256 `ddfc3dce86506e36e73103f2e7cc20715f2501bf0a1b66782f550528690dad45`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
