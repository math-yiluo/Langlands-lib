# Hilbert class fields are unramified

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that the selected big and small Hilbert class fields of a number field `K` are unramified: the big one at every finite prime, the small one at every finite prime and at every infinite place. It does so for any finite abelian extension whose idèle-class norm range is the corresponding intrinsic norm subgroup, then applies this to the selected fields over `K`.

## Main results

For a finite abelian Galois extension `L/K` of number fields with `hnorm` an equality between the image of `ideleClassNorm K L` and a norm subgroup:

- `isUnramifiedAtFinitePlaces_of_normRange_eq_bigHilbertNormSubgroup`: if the norm range is `bigHilbertClassFieldNormSubgroup`, then `L/K` is unramified at every finite prime.
- `isUnramifiedAtFinitePlaces_of_normRange_eq_smallHilbertNormSubgroup`, `isUnramifiedAtInfinitePlaces_of_normRange_eq_smallHilbertNormSubgroup` and `isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup`: if it is `smallHilbertClassFieldNormSubgroup`, then `L/K` is unramified at the finite primes, at the infinite places, and so everywhere.

Specializations to the selected fields: `bigHilbertClassField_isUnramifiedAtFinitePlaces`, `smallHilbertClassField_isUnramifiedAtFinitePlaces`, `smallHilbertClassField_isUnramifiedAtInfinitePlaces`, `smallHilbertClassField_isEverywhereUnramified`, and `bigHilbertClassField_ramifiedBaseFinitePlaces_eq_empty`, `smallHilbertClassField_ramifiedBaseFinitePlaces_eq_empty`, which say that the set of ramified finite primes of the base is empty.

## Proofs

At finite primes, the imported local–global compatibility of narrow finite conductors (`ideleClassNorm_narrowFiniteConductor_eq_zero_iff_all_finitePlaces_unramified`) reduces unramifiedness to the vanishing of the narrow finite conductor of the norm subgroup, which here is the Hilbert conductorial subgroup, whose conductor is zero. At an infinite place `v`, an idèle supported at `v` is a unit at every finite place, hence lies in the small Hilbert norm subgroup, hence in the norm range; infinite-place local–global compatibility then makes every local element at `v` a norm, which the library equates with unramifiedness at infinite places. The norm-range hypotheses for the selected fields come from the reciprocity files over the original field.

## Points to watch

- Despite the module name, the file proves unramifiedness only. That every unramified abelian extension lies in a Hilbert class field is not stated here.
- The big Hilbert class field is shown unramified at finite primes only, as expected for the narrow class field.
- `IsUnramifiedAtFinitePlaces`, `IsUnramifiedAtInfinitePlaces` and `IsEverywhereUnramified` are the library's own predicates; for infinite places the docstrings describe the condition as complete splitting of every infinite place.
- The results on the selected fields use the `K`-algebra structure on them from the files over the original base.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldUnramifiedMaximality.lean`: the Lean file is the source byte for byte (SHA-256 `20cf78748dbc126171a20a9fc98661889b1220fac5e955e0502cca1de9a5fad5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
