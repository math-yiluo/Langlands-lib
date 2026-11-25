# Tate cohomology of the units of a local field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FieldUnitsHerbrand`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension with `L` a nonarchimedean local field whose valuation extends that of `K` and whose integers are the integral closure of those of `K` (`IsIntegralClosure`), and let `g` generate `Gal(L/K)`. This file computes the Tate cohomology of `Lˣ` in degrees `0` and `−1`, the field-unit part of the local class-formation axiom.

- `unitsTateH0FiniteOfIntegerUnitsHerbrand`: if the Herbrand quotient of the integer units `O_Lˣ` is defined (`hU`), then `Ĥ⁰(Gal(L/K), Lˣ)` is finite; this theorem omits `[IsGalois K L]`.
- `fieldUnits_tate_card_of_integerUnits_herbrand_eq_one`: if moreover that quotient equals `1` (`hU_one`), then `|Ĥ⁰| = [L : K]` and `|Ĥ⁻¹| = 1`.

The proof multiplies Herbrand quotients along `O_Lˣ → Lˣ → ℤ`, uses `h(ℤ) = [L : K]` and Hilbert 90, and passes to Mathlib's Tate cohomology through `CohomologyBridge`.

The hypotheses `hU` and `hU_one` stand for the result `h(G, O_Lˣ) = 1`, obtained elsewhere from a normal basis; this file does not prove it. Cyclicity of `Gal(L/K)` is assumed through `hg`, and `K`, `L` live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FieldUnitsHerbrand.lean`: the Lean file is the source byte for byte (SHA-256 `dbd4f585c00c1a3b1e9ce30c84020af1ec9384f7c41fd3488affffed21da8567`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
