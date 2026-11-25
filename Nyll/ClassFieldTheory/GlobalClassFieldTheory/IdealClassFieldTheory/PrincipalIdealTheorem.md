# Extension of ideal classes through small-Hilbert quotients

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTheorem`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. Extension of idele classes C_K → C_L preserves the small-Hilbert norm subgroups, the images of the ideles whose finite components are all local units. It therefore induces a map between the reciprocity quotients of the small Hilbert class fields of K and L. The file shows that this map is the extension of ideal classes.

## Main results

- `smallHilbertClassFieldIdeleExtensionMap K L`: the map C_K/H_K → C_L/H_L induced by `ideleClassExtension K L` (`..._mk'` evaluates it on representatives).
- `smallHilbertClassFieldIdeleExtensionMap_naturality`: under the identifications of both quotients with ideal class groups, this map is Mathlib's `ClassGroup.extendedHom (𝓞 K) (𝓞 L)`.

## Points to watch

- The header is titled "The principal ideal theorem", but this file proves only this naturality square. The capitulation statement is not proved here.
- Every declaration omits the section's Galois hypothesis, so only finiteness of L/K is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/PrincipalIdealTheorem.lean`: the Lean file is the source byte for byte (SHA-256 `8a7d5353b4e46831f4803fe0ce0257638bf04bd8a0a0e955bd7f53b9a8db4c67`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
