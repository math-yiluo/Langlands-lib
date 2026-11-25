# Transporting global reciprocity to a model of the quotient

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file packages, once and for all, the step shared by the four Hilbert class field reciprocity files (big or small Hilbert class field, over its realized base or over the original field): given the reciprocity isomorphism between a Galois group and an idèle-class quotient, replace the quotient by a group `I` known to be isomorphic to it.

## Main definitions and results

Let `E/F` be a finite abelian Galois extension of number fields (`[FiniteDimensional F E] [IsAbelianGalois F E]`), `H` a subgroup of the idèle class group `C_F`, `h` a proof that the image of the idèle-class norm `ideleClassNorm F E` equals `H`, and `f : C_F ⧸ H ≃* I`.

- `hilbertClassFieldGlobalReciprocityTransportEquiv H h f : Gal(E / F) ≃* I`: the multiplicative form of `globalReciprocityEquiv F E`, followed by the identification of quotients given by `h`, followed by `f`.
- `hilbertClassFieldGlobalReciprocityTransport_globalNormResidue`: this isomorphism sends the global norm-residue symbol `globalNormResidueMonoidHom F E c` to `f (c mod H)`.
- `hilbertClassFieldGlobalReciprocityTransportData`: the isomorphism and this evaluation formula bundled in a subtype, the form the specializations use.
- `hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative`: the idèle class group of a number field is commutative; it is stated as a theorem and installed only as a local instance.
- `hilbertClassFieldQuotientTransport_inverse_apply_with`: a helper lemma on applying an additive equivalence followed by its inverse inside the quotient transport.

The evaluation formula holds because `globalReciprocityEquiv F E` unfolds by definition to the inverse of `globalNormResidueEquiv F E`, which is linked to `globalNormResidueMonoidHom` by `globalNormResidueMonoidHom_apply`.

## Points to watch

- Nothing about reciprocity is proved here: the reciprocity isomorphism and the norm-residue symbol come from the imports. The file only composes isomorphisms and evaluates the composite.
- The commutativity of the idèle class group is not a global instance; files that need it declare their own local instance from the theorem above.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/Transport.lean`: the Lean file is the source byte for byte (SHA-256 `483903187f0632f86fa8dc5974b8f4dd369c510e71e4e8021211eb64063fd120`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
