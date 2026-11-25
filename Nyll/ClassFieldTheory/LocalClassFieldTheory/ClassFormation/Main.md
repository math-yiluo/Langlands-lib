# The local class-field axiom

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of nonarchimedean local fields with cyclic Galois group, the file proves that the Tate cohomology of `Lˣ` has order `[L : K]` in degree 0 and order 1 in degree −1. The valuation of `L` extends that of `K`, and `𝒪_L` is the integral closure of `𝒪_K`, finite over it; both are instance hypotheses.

- `exists_localIntegerUnitsHerbrandDefinedAndEqOne`: for a generator `g`, the Herbrand quotient of `𝒪_Lˣ` is defined and equals 1.
- `localFieldUnitsTateH0FiniteOfGenerator`, `localFieldUnitsTateH0FiniteOfIsCyclic`: `Ĥ⁰(Gal(L/K), Lˣ)` is finite.
- `localFieldUnits_tate_card_of_generator`, `localFieldUnits_tate_card_of_isCyclic`: `Nat.card Ĥ⁰ = [L : K]` and `Nat.card Ĥ⁻¹ = 1`, for a given generator or under `IsCyclic`.

The proof takes a normal-basis level beyond three thresholds: existence of the principal-unit subgroup `V`, vanishing of its Herbrand groups, and the integer-unit computation. `fieldUnits_tate_card_of_integerUnits_herbrand_eq_one` then passes from `𝒪_Lˣ` to `Lˣ`.

In Lean, `K` and `L` are taken in `Type` (universe 0), and `L` carries a `UniformSpace` structure with `IsUniformAddGroup`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Main.lean`: the Lean file is the source byte for byte (SHA-256 `4699231f08d4685760d558e9fb1d3e1710c0c74d435c538206027f8b56b933d0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
