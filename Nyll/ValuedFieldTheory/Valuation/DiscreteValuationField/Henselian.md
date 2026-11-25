# Henselian discretely valued fields and idempotent lifting

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file introduces Henselian discretely valued fields as a structure over the library's discretely valued fields, and proves that idempotents lift modulo a Henselian ideal, as Hensel's lemma for the polynomial `X² − X`.

## Idempotent lifting

- `exists_idempotent_lift_of_surjective_henselianRing_ker`: if `f : R →+* S` is surjective and `R` is Henselian along `ker f` (Mathlib's `HenselianRing`), every idempotent of `S` is the image of an idempotent of `R`.
- `exists_idempotent_lift_of_henselianRing_mk` and `exists_idempotent_lift_of_henselianRing`: for `R` Henselian along `I`, an element whose class in `R ⧸ I` is idempotent is congruent modulo `I` to an idempotent of `R`; equivalently every idempotent of `R ⧸ I` has an idempotent representative.

The proof applies Mathlib's simple-root Hensel property to the monic polynomial `X² − X`: at an idempotent the derivative `2X − 1` squares to `1`, so it is a unit. Three helper lemmas record monicity, the approximate root, and the unit derivative. The zero ring is treated separately.

## Henselian DVFs

- `HenselianDVF K`: a `DVF` structure on `K` (the library's discretely valued field) together with an instance that its valuation ring is Henselian along its maximal ideal.
- Abbreviations `valuationSubring`, `maximalIdeal`, `residueField`, `residueMap`, inherited from the underlying `DVF`.
- `exists_polynomial_lift_residue`: every polynomial over the residue field lifts coefficientwise to the valuation ring.
- `valuationSubring_isDiscreteValuationRing`, `henselianRing`, `maximalIdeal_ne_bot`: the valuation ring is a DVR, is Henselian, and has nonzero maximal ideal.
- `exists_lift_root_simple`: Hensel's lemma in Mathlib's simple-root form for a monic polynomial over the valuation ring.

## Caveats

`HenselianDVF` is the library's own structure, not a Mathlib class; Henselianity is imposed as a field of the structure, not derived from completeness here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean`: the Lean file is the source byte for byte (SHA-256 `3797947f76b8884d72f9833efd81adb7a73a4de10bb4dce5a4ef58dbba36dc54`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
