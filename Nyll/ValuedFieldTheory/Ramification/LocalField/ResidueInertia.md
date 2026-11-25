# Local inertia as the kernel of the residue action

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.ResidueInertia`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` and `L` be nonarchimedean local fields and `L/K` a finite Galois extension. This file identifies the ramification group at index `0` with the kernel of the action of `Gal(L/K)` on the residue field of the canonical integer ring `𝒪[L]`.

- `localLowerRamificationGroup_zero_eq_residue_ker`: `localLowerRamificationGroup K L 0` equals the kernel of `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`.
- `localUpperRamificationGroup_zero_eq_residue_ker`: the same for the upper group at `0`. Upper and lower numbering agree at nonpositive indices.

The proof uses uniqueness of the extension of the valuation to replace the valuation ring chosen on `L` by the canonical one. Then `σ` lies in the lower group at `0` exactly when `σ(a) − a` lies in the maximal ideal for every integer `a`, which is membership in the kernel.

Both theorems carry three hypotheses as instance arguments rather than deriving them:
- the valuation of `K` extends to that of `L`;
- `𝒪[L]` is the integral closure of `𝒪[K]` in `L`;
- `𝒪[L]` is a finite `𝒪[K]`-module.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean`: the Lean file is the source byte for byte (SHA-256 `cb31c1d8ff1545f69975f48db72ad7c136fc26f3f8abd5d7b74cd1b08e91080e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
