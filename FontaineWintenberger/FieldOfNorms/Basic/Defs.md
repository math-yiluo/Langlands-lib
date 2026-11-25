# The field of norms: multiplicative structure

Module `FontaineWintenberger.FieldOfNorms.Basic.Defs`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For an arbitrary field extension `L/K`, the file defines the underlying set of the field of norms as a multiplicative object: the families `(x_E)`, indexed by all finite intermediate fields `E` of `L/K`, that are compatible under the field norms `N(F/E)` from `F` to `E`. Only the multiplication is treated here; addition, the field structure and the valuation come in later files.

## Definitions

- `FieldOfNorms.normCompatibleUnits K L`: the subgroup of the product of the unit groups `Eˣ` consisting of families `x` with `N(F/E)(x_F) = x_E` for all `E ≤ F` (via `FiniteIntermediateField.normUnits`).
- `FieldOfNorms K L`: `WithZero` of that subgroup, that is, the compatible unit families with a zero adjoined. It carries a `CommGroupWithZero` structure and is nontrivial.
- `FieldOfNorms.coord K L E`: the coordinate at `E`, a monoid-with-zero homomorphism `FieldOfNorms K L →*₀ E`.
- `FieldOfNorms.ofCofinal`: the element determined by compatible coordinates given only on a cofinal family of finite intermediate fields.

## Results

- `FieldOfNorms.coord_eq_zero_iff`: a coordinate vanishes iff the element is `0`.
- `FieldOfNorms.ext`: two elements with the same coordinates at every `E` are equal.
- `FieldOfNorms.coord_norm`: `N(F/E)(coord F x) = coord E x` for `E ≤ F`.
- `existsUnique_fieldOfNorms_of_compatible`: every family `f E ∈ E` with `N(F/E)(f F) = f E` is the coordinate family of a unique element.
- `FieldOfNorms.ext_cofinal`: if `P` is a predicate on finite intermediate fields such that every `E` lies below some `F` with `P F`, then coordinates at the fields satisfying `P` determine the element.
- `existsUnique_fieldOfNorms_of_compatible_cofinal`: a norm-compatible family given on such a `P` extends uniquely to an element.
- `FieldOfNorms.coord_ofCofinal`, `FieldOfNorms.coord_ofCofinal_of_le`: the element `ofCofinal` has the prescribed coordinates on `P`, and its coordinate at any `E` is the norm of the prescribed coordinate at any `F ≥ E` with `P F`.

## Proofs

A compatible family is zero everywhere or nowhere, since a norm vanishes only at zero; this is tested at the bottom field `K`. For a cofinal family, the coordinate at `E` is defined as a norm from a chosen larger field in `P`, and transitivity of norms shows independence of the choice.

## Points to watch

- No APF, normality or valuation hypothesis is made: the object is defined for every extension of fields, and at this stage it is only a commutative group with zero.
- The inverse system runs over all finite intermediate fields, not over a tail or a tower; the cofinality statements allow restriction to such.
- `FieldOfNorms` is a `def`, not a reducible abbreviation of `WithZero ...`; later structures are instances attached to this name.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Basic/Defs.lean` (SHA-256 of the source file `7ba39eebc72c523fbe574f4de10baa6575ee8535ba4274b13f9acf1234221ae2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
