# The conductor of an abelian extension detects exactly its ramification

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite abelian extension of number fields. The file shows that the conductor of the norm group `N C_L ⊆ C_K` is supported exactly on the ramified places. At a finite place `v`, the exponent of the minimal narrow finite conductor equals the local conductor exponent of the chosen completion above `v`. A real place lies in the infinite part of the conductor iff it ramifies (becomes complex) in `L`.

## Finite places

- `ideleClassNormDefiningModulus_le_narrowFiniteConductor` and `ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus`: the minimal narrow finite conductor `ideleClassNormNarrowFiniteConductor` equals the modulus `ideleClassNormDefiningModulus` built from the chosen local norm groups. The new inequality uses the imported compatibility between the global norm-residue map and the chosen local Artin map on one-place ideles: higher unit groups of conductor level are local norms.
- `ideleClassNorm_narrowFiniteConductor_apply_eq_chosenLocalConductorExponent`: pointwise, the conductor exponent at `v` is the chosen local conductor exponent.
- `ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces` and `ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces`: the support is the set of finite places of `K` ramified in `L`.
- `..._eq_zero_iff_all_finitePlaces_unramified` (for both moduli): the modulus is `0` iff every prime of `𝓞 L` is unramified over `𝓞 K`.

## Infinite places

- `infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn`: the archimedean norm image at `v` is all of `K_vˣ` iff `v` is unramified in `L`; in the ramified case `K_v ≅ ℝ`, `L_w ≅ ℂ`, and `-1` is not a norm.
- `ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus`: the infinite part of the full conductor is the set of real places ramified in `L`.
- `infiniteTensorNormSubgroups_eq_top_iff_isUnramifiedAtInfinitePlaces` and `ideleClassNorm_everywhereUnramified_iff_conductor_zero_and_infiniteNorms_top`: `L / K` is unramified everywhere iff the narrow finite conductor is `0` and every archimedean norm image is full.

## Restatements

In the namespace `ClassFieldTheory`: `abelianFullConductor_finiteExponent_eq_localConductorExponent`, `abelianFullConductor_finiteExponent_eq_zero_iff_unramified` (exponent `0` iff the chosen local extension is unramified), and `abelianFullConductor_mem_infinitePart_iff_realRamified`.

## Points to watch

- The narrow finite conductor records only finite exponents; in the everywhere-unramified criterion the archimedean part is handled by a separate clause, which is why that criterion has two conjuncts.
- The narrow finite conductor and the norm-defining modulus are the library's own notions; local statements are about a chosen place above `v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/AbelianConductorExactness.lean`: the Lean file is the source byte for byte (SHA-256 `609be5510b5517c0a47639ae287a025ee1c797da8bbc9c6ea42cc270175cdc81`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
