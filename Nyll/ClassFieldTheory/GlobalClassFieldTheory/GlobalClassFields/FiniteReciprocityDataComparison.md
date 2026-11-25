# Finite reciprocity data recover the global norm-residue map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteReciprocityDataComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields, and let `D : FiniteAbelianReciprocityData K L` be a datum: a modulus outside which L/K is unramified and a ray-class Artin map sending each prime outside the modulus to its arithmetic Frobenius. This file shows that D determines the global reciprocity map on all of C_K.

- `originalArtin_prime`: for a prime p outside the modulus, the Artin map of D, read on the idèle-class form of the ray class group, sends the class of the one-place prime idèle at p to `arithmeticFinitePlacePrimeArtin p`.
- `ideleClassArtin D`: the composite C_K → ray class group → Gal(L/K), with no new choice of Artin map.
- `ideleClassArtin_apply` and `ideleClassArtin_eq_arithmeticGlobalNormResidue`: this homomorphism equals the library's arithmetic global norm-residue homomorphism, as homomorphisms and not only through their kernels.

The equality uses the imported ray Frobenius rigidity theorem `rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue`: a homomorphism on a ray class group with the right prime values agrees with the norm-residue map everywhere, ramified places included.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FiniteReciprocityDataComparison.lean`: the Lean file is the source byte for byte (SHA-256 `33b1c9f53b702cd2711b12bb78af6aa4f1ea910c749ed7848f9870798470e1a9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
