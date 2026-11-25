# The principal-unit filtration

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a valuative relation, valuation ring `𝒪[K]` and maximal ideal `𝓂[K]`, this file defines the principal-unit filtration `U^n = {u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂^n}` and the quotients `𝒪[K]ˣ/U^n`.

## Definitions and results

- `principalUnits K n`: the subgroup `U^n` of `𝒪[K]ˣ`; `mem_principalUnits_iff` unfolds membership. `principalUnits_zero`: `U^0` is all of `𝒪[K]ˣ`. `principalUnits_antitone`, `principalUnits_succ_le`, `principalUnits_le_one`: the filtration decreases.
- `principalUnits_map_ringEquiv`: a ring isomorphism `𝒪[K] ≃ 𝒪[L]` carries `U^n` of `K` onto `U^n` of `L`.
- `principalUnits_integerRingEquiv_mem`: an automorphism of `𝒪[K]` that maps `𝓂^n` into itself maps `U^n` into itself.
- `IntegerUnitsPrincipalQuot K n`: the commutative group `𝒪[K]ˣ/U^n`, with quotient map `integerUnitsPrincipalQuotMk`, lifting `integerUnitsPrincipalQuotLift`, induction principle, kernel and equality criteria (two units have the same class exactly when their quotient lies in `U^n`), and `integerUnitsPrincipalQuotConcreteEquiv` to the concrete `QuotientGroup` quotient.
- Helpers: the identity `ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)` and antitonicity of `𝓂^n`.

## Points to watch

- Only `[Field K] [ValuativeRel K]` is assumed; no local-field hypothesis.
- `principalUnits_integerRingEquiv_mem` takes preservation of `𝓂^n` as a hypothesis.
- The module comment speaks of the quotient by the first filtration step, but `IntegerUnitsPrincipalQuot K n` is defined for every `n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`: the Lean file is the source byte for byte (SHA-256 `1ed988cff62846232aa7cc265df51ecf9ce83dffbc6111bd79335644ecb08af0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
