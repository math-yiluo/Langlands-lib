# Galois-fixedness of finite-level representatives

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPointDescentCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file supplies the finite-level ingredients for descending fixed elements of `rationalIdeleClassDirectLimit`: a class at a finite Galois level `U` that is fixed in the limit by `Gal(ℚˢᵉᵖ/K)` becomes, after base change to the tower `ℚ ⊆ K ⊆ U`, a class fixed by `Gal(U/K)`, and such classes are identified with the idele class group of `K`.

## Main definitions

The setting is a finite intermediate field `K` of `ℚˢᵉᵖ/ℚ` and a finite Galois intermediate field `U`, with a `K`-algebra structure on `U` that is finite and Galois.

- `rationalRelativeIdeleClassTowerBaseChangeEquiv K U`: the multiplicative equivalence from `RelativeIdeleGroup.ClassGroup ℚ U` to `RelativeIdeleGroup.ClassGroup K U`, through the tower presentation.
- `rationalIntermediateIdeleClassEquivGaloisFixed K U`: `C_K` is equivalent to `RelativeIdeleGroup.galoisFixedClassSubgroup K U`, the classes fixed by `Gal(U/K)`; the simp lemma `rationalIntermediateIdeleClassEquivGaloisFixed_coe` says it is `RelativeIdeleGroup.classInclusion K U`.

## Main results

- `rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed`: if the algebra map `K → U` agrees with the inclusions in `ℚˢᵉᵖ`, `z` is the class of `d` at level `U`, and every `σ` fixing `K` fixes `z`, then the tower base change of `d` is fixed by `Gal(U/K)`.
- `rationalIntermediateField_algebra_eq_inclusion`: an algebra structure `K → U` agreeing with the inclusions is the one induced by the inclusion.

## Proofs

Each `η ∈ Gal(U/K)` lifts to some `σ ∈ Gal(ℚˢᵉᵖ/ℚ)`, which fixes `K`; injectivity of the level map into the limit gives `σ|_U • d = d`, and the tower base change is equivariant.

## Points to watch

- `rationalIntermediateIdeleClassEquivGaloisFixed` transports the imported equivalence `RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed`; the statement that `C_K` is the `Gal(U/K)`-fixed part of the idele classes of `U` is not proved here.
- The compatibility of the `K`-algebra structure on `U` with the ambient inclusions is a hypothesis, not built in.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitFixedPointDescentCore.lean`: the Lean file is the source byte for byte (SHA-256 `bc1bd5eb4c79a93945bb27e8a91f9537e445fa66c1d49d3bb288991c63e84579`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
