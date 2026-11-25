# Prime classes generate the ray class group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayPrimeGeneration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that the classes of primes not dividing a modulus generate the ray class group, in the form of an extensionality principle for homomorphisms.

- `rayClassGroup_hom_ext_finitePrime`: let `m` be a modulus of a number field `K` and `f`, `g` two monoid homomorphisms from the idelic ray class group `RayClass.RayClassGroup m` to a monoid `G`. If `f` and `g` agree on the class of the prime idèle `finitePrimeIdele v` for every prime `v` outside the finite support of `m`, then `f = g`.

The proof passes to the ideal ray class group through the library's isomorphism `rayClassGroupEquivIdealRayClassGroup`, under which the prime idèle class corresponds to the class of the prime ideal of `v`. There it applies the imported extensionality lemma for homomorphisms out of the group of fractional ideals prime to `m`, which rests on unique factorization into primes.

The target `G` need only be a monoid; no commutativity is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayPrimeGeneration.lean`: the Lean file is the source byte for byte (SHA-256 `bdef92957ecf822aec9583400d55802e23fcc475afe6d3ecb699950c1ebd6ff2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
