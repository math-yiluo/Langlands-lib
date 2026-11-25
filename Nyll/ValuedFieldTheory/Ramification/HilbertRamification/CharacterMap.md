# The inertia character σ ↦ χ_σ and the ramification group

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a field extension and `A` a valuation subring of `L`, with decomposition, inertia and ramification groups `D`, `I`, `R` taken from the library's ramification-group file. For `σ` in `D` the file studies the quotient `σx/x` (`automorphismUnitQuotient`) for `x : Lˣ`, and builds from it the canonical map from the value-trivial part of inertia to characters of a "value group modulo base value group" with values in the residue units `λˣ`, whose kernel is the ramification group.

## Main content

- `inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup`: for `σ ∈ I` and `u` a unit of `A`, `σu/u` is a principal unit (lies in `U¹`).
- `inertiaUnitQuotientClass`: the class of `σx/x` in `Lˣ/U¹`. It is unchanged when `x` is multiplied by a unit of `A` or by the image of a unit of `K`. `mem_ramificationGroup_iff_forall_inertiaUnitQuotientClass_eq_one`: `σ ∈ R` iff all these classes are trivial.
- `inertiaUnitQuotientHom`, `valueClassToPrincipalUnitQuotient`, `valueModuloBaseToPrincipalUnitQuotient`: the raw map `x ↦ [σx/x]` as a homomorphism on `Lˣ`, then descended to `Lˣ/Aˣ` and to `(Lˣ/Aˣ)/(image of Kˣ)`.
- `valueDisplacementClass`, `valueDisplacementHom`: the class of `σx/x` in `Lˣ/Aˣ`; trivial for `σ ∈ R`.
- `valueTrivialInertiaGroup`: the subgroup of `I` of those `σ` with `σx/x ∈ Aˣ` for every `x`; it contains `R`.
- `valueTrivialInertiaResidueUnitHom`: for such `σ`, the homomorphism `χ_σ : Lˣ → λˣ`, `x ↦ σx/x mod 𝔪`. It kills `Aˣ` and `Kˣ` and descends to `valueModuloBaseToResidueUnits` on `(Lˣ/Aˣ)/(image of Kˣ)`.
- `valueTrivialInertiaCharacterHom`: the group homomorphism `σ ↦ χ_σ` from the value-trivial inertia group to `Hom((Lˣ/Aˣ)/Kˣ, λˣ)`; multiplicativity rests on `χ_σ` being unchanged when its argument is moved by another value-trivial inertia element.
- `valueTrivialInertiaCharacterHom_mem_ker_iff`: its kernel is exactly the ramification group (intersected with the value-trivial subgroup).

## Points to watch

- The character map is defined only on `valueTrivialInertiaGroup`, not on all of `I`. The file's comment says that for the stabilizer form of the decomposition group value-triviality is a genuine condition; the file does not prove that it holds for all of inertia.
- The usual `Δ/Γ` is modelled group-theoretically as `(Lˣ/Aˣ)/(image of Kˣ)`; it is not identified here with a quotient of value groups, and surjectivity of `σ ↦ χ_σ` is not addressed.
- No finiteness, Galois or completeness hypotheses appear in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/CharacterMap.lean`: the Lean file is the source byte for byte (SHA-256 `a0f790204890a5e4da85dffa1b166c9d27fa7a4de7b54cdc002478cd2e7768da`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
