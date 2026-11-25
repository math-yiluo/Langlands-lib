# Ramification and the vanishing of abelian norm moduli

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorRamification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension of number fields `L / K`, the file relates the modulus `ideleClassNormDefiningModulus`, built from the chosen local norm groups, and the minimal narrow finite conductor `ideleClassNormNarrowFiniteConductor` to ramification of the chosen completions above each finite place.

- `ideleClassNormDefiningModulus_eq_zero_iff_all_chosenFinitePlaces_unramified`: the defining modulus is `0` iff the chosen completed extension is unramified at every finite place; `..._ne_zero_iff_exists_chosenFinitePlace_ramified` is the negated form.
- `mem_ideleClassNorm_narrowFiniteConductor_support_imp_chosenFinitePlace_ramified`: every place in the support of the narrow finite conductor is ramified in the chosen completion.
- `ideleClassNorm_narrowFiniteConductor_eq_zero_of_all_chosenFinitePlaces_unramified`: if all chosen completions are unramified, the narrow finite conductor is `0`.

The proofs use the imported pointwise description of the defining modulus by local higher-unit exponents and the inequality conductor ≤ defining modulus.

Only the inclusion of the conductor's support in the ramification locus, and one direction of the vanishing criterion, are proved for the conductor here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/AbelianConductorRamification.lean`: the Lean file is the source byte for byte (SHA-256 `a1187a99843480c7fa7d9d68a11b7021d537781e9ce61094b532e9e7880cbb5e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
