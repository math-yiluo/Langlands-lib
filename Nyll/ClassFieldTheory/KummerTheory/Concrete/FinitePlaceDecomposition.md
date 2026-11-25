# Kummer radicals and decomposition fields at finite places

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.FinitePlaceDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a Galois extension, `n` a positive integer with a primitive `n`-th root of unity in `K`, and `β ∈ Lˣ` with `β ^ n = a` for some `a ∈ Kˣ`. This file shows that `a` is an `n`-th power in the completion of `K` at a place exactly when `β` lies in the decomposition field of the chosen place of `L` above it: in one direction for any nontrivial absolute value, in both directions for a finite place of a number field `K`.

## Main results

- `kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup`: for a nontrivial absolute value `vK` on `K`, an extension `w` of it to `L`, and `a` an `n`-th power in the completion `K_vK`, the element `β` lies in the fixed field of the decomposition group of `w` (`absoluteValueDecompositionGroup`). `K` need not be a number field and `L/K` need not be finite here.
- `finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField`: for `K` a number field and `v` a finite place, `a` is an `n`-th power in `(v.adicCompletion K)ˣ` if and only if `β` lies in the decomposition field of `chosenFinitePlaceExtension v`.

## Proofs

Both proofs pass to the library's algebraic localization `LocalizedCompletion vK w`, an extension of `K_vK` into which `L` maps, and use the library's identification of the elements of `L` that land in `K_vK` with the decomposition field (`localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup`). If `y ^ n = a` in the completion, then `β / y` is an `n`-th root of unity, hence a power of the given primitive root, so `β` lies in `K_vK`. Conversely, if `β` lies in `K_vK` it is itself an `n`-th root of `a` there. The finite-place statement transports along the comparison `finitePlaceCompletionUnitsContinuousMulEquiv` between the absolute-value completion and `v.adicCompletion K`.

## Remarks

- The hypothesis that `K` contains a primitive `n`-th root of unity is used in the forward direction.
- The decomposition group is the library's own, defined through absolute values (`absoluteValueDecompositionGroup`), at the chosen extension `chosenFinitePlaceExtension v` rather than at an arbitrary place above `v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/FinitePlaceDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `d143f6d4053a2cd91f787fc754f6b57bc620d26480a061a3e63ca63c89656c06`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
