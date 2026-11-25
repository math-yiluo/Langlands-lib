# The principal ideal theorem

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and H = `smallHilbertClassField K` its selected small Hilbert class field. H is a K-algebra through the fixed-field copy of K. The file proves the principal ideal theorem: every ideal of 𝓞 K becomes principal in 𝓞 H.

## Main results

- `smallHilbertClassFieldIdeleExtensionMap_eq_one`: consider the map from C_K / H_K to C_H / H_H induced by extension of idele classes, where H_K and H_H are the small-Hilbert norm subgroups of K and of H. This map is trivial.
- `smallHilbertClassFieldClassGroupExtension_eq_one`: Mathlib's extension of ideal classes `ClassGroup.extendedHom (𝓞 K) (𝓞 H)` is the trivial homomorphism.
- `allIdealsBecomePrincipalInSmallHilbertClassField`: for every ideal I of 𝓞 K, the ideal `I.map (algebraMap (𝓞 K) (𝓞 H))` is principal.
- `allFractionalIdealsBecomePrincipalInSmallHilbertClassField`: every nonzero fractional ideal of K, extended to H, lies in the range of `toPrincipalIdeal`.

## Proof

1. An imported containment theorem, proved through Witt's transfer theorem applied to the selected tower K ⊆ H ⊆ H', places every extended idele class of K in the small-Hilbert norm subgroup of H. Here H' is the small Hilbert class field of H. So the induced quotient map is trivial.
2. The naturality square between that quotient map and `ClassGroup.extendedHom` transfers triviality to ideal classes.
3. Mathlib's `ClassGroup.extendedHom_eq_one_iff_forall_ideal_map_isPrincipal` gives the statement for ideals. The fractional-ideal form uses compatibility of ideal classes with extension.

## Points to watch

The statement is for the library's selected field `smallHilbertClassField K` with its K-algebra structure, not for an arbitrary field shown to be a Hilbert class field of K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertPrincipalization.lean`: the Lean file is the source byte for byte (SHA-256 `50273d898c02bfc00a9472f90f038287010ae0e4f55080f26a9cec8a8b882f87`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
