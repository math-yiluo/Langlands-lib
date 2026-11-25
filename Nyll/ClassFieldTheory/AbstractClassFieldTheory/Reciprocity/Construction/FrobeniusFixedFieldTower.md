# Towers of Frobenius fixed fields

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Bundles used by the unit and norm computations of the universal norm-descent argument in abstract class field theory. Given a finite residue abstract field `K` for a degree map `D`, a Galois subextension `L | K` and Frobenius elements of `G_K / I_L`, the fixed fields of two Frobenius elements form a tower when one contains the other; the structures here store such a tower together with the finiteness, normality and commutation data that norm and unit-group statements need, so that downstream statements do not repeat them.

## Main definitions

- `DegreeData.frobeniusFixedAbstractField`: the fixed field of a Frobenius element `σ` as a finite abstract field, given an instance saying it has finite index in the distinguished base field `baseField G`.
- `DegreeData.FrobeniusFixedFieldTower`: an ambient base `K`, a Galois subextension `L | K`, two commuting Frobenius elements (`baseFrobenius`, `fieldFrobenius`) whose fixed fields satisfy `Σ_base ⊆ Σ_field` (supplied as the proof `field_le_base`), finiteness of `Σ_field | Σ_base` and of both fixed fields over `baseField G` (not over `K`), and normality of `Σ_field | Σ_base`. Derived objects: `base`, `field`, `toGaloisSubextension`, `extension` (a finite abstract field extension), and instances for normality and finiteness.
- `FrobeniusFixedFieldTower.Representative`: an element of `G(Σ_base)` mapping to the base Frobenius under the identification of `G(Σ_base) / I` with the Frobenius closure; `CyclicGenerator` adds that its class generates the finite quotient `Gal(Σ_field | Σ_base)`.
- `DegreeData.FiniteAmbientFrobeniusFixedFieldTower`: a tower whose ambient extension `L | K` is finite, with instances transporting this finiteness to the quotient `G_K / G_L`.
- `DegreeData.FrobeniusPowerFixedFieldTower`: a finite Galois subextension `L | K`, a Frobenius element `φ` of exponent one, an integer `n > 0`, and the finiteness of the fixed fields of `φⁿ` and `φ^(n²)` over the base field and of the one over the other. `baseFrobenius` is `φⁿ`, `fieldFrobenius` is `φ^(n²)`.

## Main results

- `frobenius_commute_base`, `frobenius_commute_field`: `φ` commutes with `φⁿ` and with `φ^(n²)`.
- `field_le_base`: the fixed field of `φ^(n²)` contains that of `φⁿ`.
- `toFrobeniusFixedFieldTower`, for `G` Hausdorff: a power tower is a fixed-field tower, normality coming from an earlier result on Frobenius power fixed fields; `toFiniteAmbientFrobeniusFixedFieldTower` keeps the finiteness of the ambient extension.

## Watch for

- The finiteness of the fixed fields over the base field is stored as data in the structures, not derived; constructing a tower requires supplying these witnesses.
- In a power tower the upper Frobenius is `φ^(n²)`, not `φ^(2n)` or a second free exponent.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean`: the Lean file is the source byte for byte (SHA-256 `802d50ac65ca8388e326c5a3ea64554f806faf71c5bd569f67deb75d8155647c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
