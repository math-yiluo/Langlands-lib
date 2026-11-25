# Residue fields of local rings under local homomorphisms

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects elementary facts on residue fields of local rings and the maps induced on them by local homomorphisms, stated for Mathlib's `IsLocalRing.ResidueField`, `IsLocalRing.residue` and `IsLocalRing.ResidueField.map`. It introduces no new notion of residue field.

## Main results

- `residue_eq_residue_iff_sub_mem_maximalIdeal`: two elements of a local ring have the same residue exactly when their difference lies in the maximal ideal.
- `lift_eq_of_comp_residue_eq`: for a local homomorphism `f : R →+* S` to a field, a map `κ(R) → S` whose composite with the residue map is `f` is Mathlib's `IsLocalRing.ResidueField.lift f`.
- For a local homomorphism `f : R →+* S` between local rings: `comap_maximalIdeal_eq` (the maximal ideal of `S` pulls back to that of `R`); `map_injective` (the induced map `κ(R) → κ(S)` is injective), with forms for zero and for equality of residues; `ringEquivOfSurjective` (the isomorphism `κ(R) ≃+* κ(S)` when the induced map is surjective); and criteria for `κ(f)(x̄) = ȳ` as `f x − y ∈ m_S`.
- For a local algebra map `R → S`: `algebraMap_eq_map_algebraMap` identifies Mathlib's residue-field algebra map with `ResidueField.map (algebraMap R S)`, and the previous facts are restated in this form.
- `algEquivOfAlgEquiv`: for local `T`-algebras `R` and `S` with local structure maps, a `T`-algebra isomorphism `R ≃ₐ[T] S` induces a `κ(T)`-algebra isomorphism `κ(R) ≃ κ(S)`. It is compatible with residues, inverses, identity and composition.

## Proofs

Lift uniqueness, injectivity and the identification of the algebra map follow by choosing residue representatives, using surjectivity of the residue map and, for injectivity, the fact that a local homomorphism pulls the maximal ideal back to the maximal ideal. The other statements follow from these, from the definitions, or from Mathlib lemmas; compatibility with composition is `IsLocalRing.ResidueField.mapEquiv_trans`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ResidueField.lean`: the Lean file is the source byte for byte (SHA-256 `a6bfeeddb4784abeefd449c160f2d1ee3b2f17710a7fc890b07de348c0510206`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
