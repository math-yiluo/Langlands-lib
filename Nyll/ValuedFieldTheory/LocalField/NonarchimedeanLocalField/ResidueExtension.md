# Residue maps and the degree formula for an extension of valued fields

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` and `L` be fields with valuative relations and `L` a `K`-algebra whose canonical valuations are compatible (`Valuation.HasExtension`). This file names the maps induced on valuation rings, residue fields and unit groups, compares the quotients `𝒪ˣ/U¹` with residue units, and, for nonarchimedean local fields, proves the degree formula `e · f = [L:K]` and surjectivity of the residue trace and norm.

## Induced maps

- `integerRingMapOfValuationExtension : 𝒪[K] →+* 𝒪[L]`, a local homomorphism; `residueFieldMapOfValuationExtension : 𝓀[K] →+* 𝓀[L]`, equal to `algebraMap`; the injective `residueUnitsMapOfValuationExtension` and `integerUnitsMapOfValuationExtension : 𝒪[K]ˣ →* 𝒪[L]ˣ`, compatible with reduction.
- `integerUnitsModPrincipalUnitsMapOfValuationExtension : 𝒪[K]ˣ/U¹_K →* 𝒪[L]ˣ/U¹_L`, compatible with the identifications with residue units. A unit of `𝒪[K]` lies in `U¹_K` exactly when its image lies in `U¹_L` (the two directions are separate lemmas).
- `integerUnitsModPrincipalUnitsResidueNormOfValuationExtension : 𝒪[L]ˣ/U¹_L →* 𝒪[K]ˣ/U¹_K`: the norm of `𝓀[L]/𝓀[K]` on residue units, transported to the quotients.

## Results for local fields

- `residueUnitsMap_residueField_norm_eq_prod_algEquiv`: the residue norm of `u`, mapped back into `𝓀[L]`, is the product of `τ u` over all `𝓀[K]`-automorphisms `τ` of `𝓀[L]`; a quotient-level version follows.
- `residueAlgEquiv_card_eq_finrank`, `maximalIdeal_inertiaDeg_eq_residue_finrank`: the automorphism group of `𝓀[L]/𝓀[K]` has order `f = [𝓀[L] : 𝓀[K]]`, and `f` is Mathlib's inertia degree of `𝓂[L]` over `𝒪[K]`.
- `maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`: for finite `L/K` with `𝒪[L]` a finite `𝒪[K]`-module, `e · f = [L:K]`, where `e` is Mathlib's `Ideal.ramificationIdx'`. The `_of_isIntegralClosure` version obtains module-finiteness from separability and `IsIntegralClosure 𝒪[L] 𝒪[K] L` (`integerRing_moduleFinite_of_isIntegralClosure`).
- `residue_finrank_eq_finrank_of_ramificationIdx_eq_one_of_isIntegralClosure` and `residueAlgEquiv_card_eq_finrank_of_ramificationIdx_eq_one_of_isIntegralClosure`: if `e = 1`, then `f = [L:K]` and the residue automorphism group has order `[L:K]`.
- `residueField_trace_surjective_of_valuationExtension`, `residueField_units_norm_surjective_of_valuationExtension` and `integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension`: the residue trace, and the residue norm on units and on the quotients, are surjective.

## Proofs

The degree formula is Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`, using that `𝓂[L]` is the only prime of `𝒪[L]` over `𝓂[K]`. The residue statements are Mathlib facts on finite fields and Galois extensions.

## Points to watch

- The quotient-level residue norm is not the field norm on units; its comment says that its compatibility with `normIntegerUnits` is a later step, and that compatibility is not proved here.
- Finiteness of `𝒪[L]` over `𝒪[K]` (or integral closure with separability) and, for the unramified results, `e = 1` are hypotheses.
- The module comment mentions Frobenius results, but no declaration here concerns a Frobenius element.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`: the Lean file is the source byte for byte (SHA-256 `2776dfb96703399e38515335ec8ff8b93c33c0972888632578821928ff88a223`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
