# Norms on unit groups and valuation rings

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file collects facts about the field norm `Algebra.norm K : L → K` of an extension `L/K`, viewed on unit groups and on valuation rings. The main point is that the norm of an element of `𝒪[L]` lies in `𝒪[K]`, so that the norm restricts to a homomorphism `𝒪[L]ˣ →* 𝒪[K]ˣ`.

## Contents

- `mapBaseUnitsToExtensionUnits K L : Kˣ →* Lˣ`, the inclusion of units. `normUnits_algebraMap_base` and `normUnits_mapBaseUnitsToExtensionUnits_apply_coe`: the norm of an embedded base unit is its `[L:K]`-th power. `normUnits_algEquiv_apply`: the norm on units is invariant under `K`-automorphisms of `L`.
- `algebraNorm_mem_integers_of_mem_integers`: under the class `ValuativeExtension K L`, `N(x) ∈ 𝒪[K]` for every `x ∈ 𝒪[L]`. Variants assume instead `IsIntegralClosure 𝒪[L] 𝒪[K] L`, or only that `x` is integral over `𝒪[K]` (`algebraNorm_mem_integers_of_isIntegral`).
- `normIntegerUnits K L : 𝒪[L]ˣ →* 𝒪[K]ˣ`, the norm restricted to units of the valuation ring; `normIntegerUnits_apply_coe` says its value is the algebra norm, and `normIntegerUnitsValue` is the underlying element of `𝒪[K]`.
- `mapBaseUnits_normUnits_eq_prod_gal`: for a finite Galois extension, the norm of `x ∈ Lˣ`, embedded back into `Lˣ`, is the product of the conjugates `σ x` over all `σ` in the Galois group.
- Linear-algebra helpers: left multiplication by a nonzero element is injective and surjective, and a bijective `K`-linear endomorphism of `L`, when `L` is finite and free over `K`, has nonzero determinant.

## Proofs

Integrality of the norm comes from Mathlib's `Algebra.isIntegral_norm` and the integral closedness of the valuation ring `𝒪[K]`; the Galois formula is Mathlib's `Algebra.norm_eq_prod_automorphisms`.

## Points to watch

- `normUnits` is defined in an imported file, and `ValuativeExtension` is this library's own class, not a Mathlib notion. What the file uses of it is `ValuativeExtension.integer_isIntegral`: every element of `𝒪[L]` is integral over `𝒪[K]`. So the integrality behind `algebraNorm_mem_integers_of_mem_integers` and `normIntegerUnits` is a hypothesis carried by the class, not a result of this file.
- `mapBaseUnits_normUnits_eq_prod_gal` sits in a section with local-field hypotheses but uses none of them: it holds for any finite Galois extension of fields.
- Despite its name, `valuation_norm_le_one_of_integer` only says that an element of `𝒪[K]` has valuation at most one; no norm occurs in it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`: the Lean file is the source byte for byte (SHA-256 `661f316f9d36d09f792f8624025d5a573b0e5865e8afe50db3a87802e48c30bb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
