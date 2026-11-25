# Local–global compatibility for cyclotomic unramified extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedLocalGlobalCompatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The setting is abstract class field theory over ℚ with the cyclotomic degree datum. Let `H` be a finite abstract field with fixed number field F, and `L` a finite abelian subextension, unramified for `rationalCyclotomicDegreeData`, with fixed field E. The file shows that at every finite place v of F the global norm residue homomorphism C_F → Gal(E/F) agrees with the chosen local Artin homomorphism at v. The comparison uses the idele class of the one-place idele with component x at v and 1 elsewhere.

## Main results

- `abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass`: under the unramifiedness hypothesis `hUnramified`, `abstractFixedFieldGlobalNormResidueMonoidHom H L` composed with `IdeleGroup.finitePlaceIdeleClass v` equals `chosenFinitePlaceArtinMonoidHom` of E/F at v.
- `globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified`: the same for `globalNormResidueMonoidHomOfEmbedding F E j`, with j the inclusion of E into `SeparableClosure ℚ`.

## Proof

The proof chains four identities:
- the global norm residue map is restriction after the cyclotomic idele-class Artin map (`abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction`, from another file);
- on a one-place idele class, the idele-class Artin map is the infinite Artin map of U/F at the one-place idele, where U is the cyclotomic maximal unramified field;
- restriction from U to E turns the infinite Artin map into the finite global Artin map of E/F; a private lemma proves this for a scalar tower K ⊆ E ⊆ Ω with K and E number fields in `Type` and E/K, Ω/K abelian Galois;
- the finite global Artin map on a one-place idele is the chosen local factor (`globalArtinMonoidHom_finitePlaceIdele`).

## Watch for

- The statement covers only subextensions that are unramified in the sense of the abstract degree datum, and only finite places.
- The local maps are the library's chosen local Artin homomorphisms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicUnramifiedLocalGlobalCompatibility.lean`: the Lean file is the source byte for byte (SHA-256 `390ee8420ec63bc86e9c3c2aaa168119332a205d9942f8b97ac91fa2b79afa31`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
