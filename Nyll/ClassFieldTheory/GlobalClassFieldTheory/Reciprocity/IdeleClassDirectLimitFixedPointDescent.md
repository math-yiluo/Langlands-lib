# Descent of fixed elements of the rational idele-class direct limit

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPointDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that an element of `rationalIdeleClassDirectLimit` fixed by `Gal(ℚˢᵉᵖ/K)`, for a finite intermediate field `K`, comes from the idele class group `C_K`: first at one finite Galois level, then in the direct limit.

## Main results

For a finite intermediate field `K` and a finite Galois intermediate field `U` containing it, with a finite Galois `K`-algebra structure on `U` agreeing with the inclusions in `ℚˢᵉᵖ`:

- `rationalRelativeIdeleClass_descent_square`: for `q ∈ C_K`, the tower base change of the scalar extension of `q` to `U` (through the relative presentation over `ℚ`) is `RelativeIdeleGroup.classInclusion K U q`.
- `rationalRelativeIdeleClass_exists_descent_of_tower_fixed`: if `d` is a relative idele class at `U` whose tower base change is fixed by `Gal(U/K)`, then `d` is the scalar extension of some `q ∈ C_K`.

In the direct limit:

- `rationalDirectLimit_fixed_exists_ideleClass`: if `z` is fixed by every `σ` in `K.fixingSubgroup`, then `z = rationalIntermediateIdeleClassToDirectLimit K q` for some `q ∈ C_K`.

## Proofs

The descent at level `U` reads off `q` from `rationalIntermediateIdeleClassEquivGaloisFixed` and uses the commuting square. In the limit, `z` is represented at some level `E`; one moves to the compositum `U` of `E` and the normal closure of `K`, applies `rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed`, then descends.

## Points to watch

- Only existence of a preimage is proved here; injectivity and the equivalence of `C_K` with the fixed part are proved elsewhere.
- The fixedness hypothesis is quantified over `K.fixingSubgroup`, as a subgroup of all `ℚ`-automorphisms of `ℚˢᵉᵖ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitFixedPointDescent.lean`: the Lean file is the source byte for byte (SHA-256 `124e5ed4226021ab5966fb0b0c359102c31e50080831d2c24aa94784ffd5f3fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
