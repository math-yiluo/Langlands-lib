# Galois actions and the valuation sequence of a local field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an extension `L/K` of fields with valuative relations, the valuation of `L` extending that of `K` and `𝒪_L` the integral closure of `𝒪_K`, the file defines the Galois actions on `Lˣ`, `𝒪_Lˣ` and the value group `ℤ`, and shows that the valuation sequence `𝒪_Lˣ → Lˣ → ℤ` is compatible with them. The valuation results assume that `L` is a nonarchimedean local field.

## Definitions

- `galoisGroupFieldUnitsMulDistribMulAction`: `Gal(L/K)` acting on `Lˣ` by applying automorphisms.
- `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`: the action on `𝒪_Lˣ`, through the restriction of automorphisms to the integral closure (`galoisGroupIntegerRingEquivOfIsIntegralClosure`).
- `galoisGroupValueGroupMulDistribMulAction`: the trivial action on `Multiplicative ℤ`.

## Results

- `integerUnitsToFieldUnits_galoisGroup_equivariant`: the inclusion `𝒪_Lˣ → Lˣ` is equivariant.
- `valuationMap_unitsMapEquiv_galoisGroup`: every `σ ∈ Gal(L/K)` preserves the normalized valuation `valuationMap L` on `Lˣ`.
- `valuationUnitsMulHom_galoisGroup_equivariant`: the valuation `Lˣ → Multiplicative ℤ` is equivariant for the trivial action on `ℤ`.
- `valuationUnitsMulHom_eq_one_iff_exists_integerUnit`, `integerUnitsToFieldUnits_range_eq_ker_valuationUnitsMulHom`: the kernel of the valuation is the image of `𝒪_Lˣ` (exactness at `Lˣ`); `valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero` relates the multiplicative and additive forms.
- `valuationUnitsMulHom_surjective`: the valuation `Lˣ → ℤ` is surjective.

## Proofs

Invariance of the valuation writes `x = u · ϖⁿ` with `u ∈ 𝒪_Lˣ` and `ϖ` the field unit `inverseIntegerRingUniformizerFieldUnit`. Since `σ` restricts to a ring automorphism of `𝒪_L`, it maps the uniformizer to an irreducible element and units to units, so the valuation of `σ(x)` is again `n`. No invariance of the extended valuation is assumed. Exactness and surjectivity are taken from results on the valuation sequence proved elsewhere.

## Points to note

- In the proof, irreducible elements of `𝒪_L` have valuation −1 and `ϖ`, the inverse of the uniformizer, has valuation 1; the sign convention of `valuationMap` is thus opposite to that of the usual order function. The statements of this file do not depend on it.
- The actions are definitions marked `@[implicit_reducible]`, not instances, and are fixed in each statement as local instances.
- The action on `Lˣ` allows `K` and `L` in different universes; the other declarations involving both fields take them in the same universe (`K L : Type u`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`: the Lean file is the source byte for byte (SHA-256 `3b847927ca074ff003e37f78a6b396cf6845b6dcfecfe5fe10c07649c77edbdb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
