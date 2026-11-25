# Frobenius normalization of the Artin map in any universes

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an unramified finite abelian extension L/K of nonarchimedean local fields, with K : Type u and L : Type v, the file shows that the universe-polymorphic Artin map `LocalClassFieldTheory.Universe.abelianLocalArtinMap` is given by powers of arithmetic Frobenius. The native result for small copies `Shrink.{0} K`, `Shrink.{0} L` is carried over, using identifications of their valuation rings and residue fields with the original ones.

Hypotheses: K and L each carry `ValuativeRel`, a topology and `IsNonarchimedeanLocalField`; the valuation of L extends that of K (`Valuation.HasExtension`); `FiniteDimensional K L`, `IsAbelianGalois K L` and `IsUnramifiedValuedExtension K L`.

## Main results

- `shrink_isUnramifiedValuedExtension`: the small copies again form an unramified valued extension; ramification index one follows from the equality 𝔪_K 𝒪_L = 𝔪_L transported along the ring equivalences.
- `abelianLocalArtinMap_inverseUniformizer_residue_pow`: if `valuationMap K π = 1`, the Artin image of π sends each x ∈ 𝒪_L to an element of 𝒪_L whose residue is (residue of x)^q, where q is the cardinality of the residue field of K.
- `abelianLocalArtinMap_uniformizer`: for such π the Artin image is `arithmeticFrobeniusOfUnramifiedValuation K L`, using that Gal(L/K) acts faithfully on the residue field.
- `abelianLocalArtinMonoidHom_integerUnit_eq_one`: units of 𝒪_K map to 1.
- `abelianLocalArtinMonoidHom_eq_frobenius_zpow`: the Artin image of x ∈ K^× is Frob raised to `valuationMap K x`, obtained by writing x as a unit times a power of π.
- `unramifiedLocalReciprocityIsoToGaloisGroup_normClass_eq_artin`: the explicit unramified reciprocity isomorphism on the norm quotient agrees with this Artin map on every class.
- `abelianLocalArtinMap_uniformizerFieldUnit`: a uniformizer of 𝒪_K maps to Frob⁻¹.
- `abelianLocalArtinMap_inverseUniformizer_residue_pow_iff`: σ ∈ Gal(L/K) acts on residues by x ↦ x^q if and only if σ is the Artin image of π⁻¹, π a uniformizer.

## Caveats

- Sign convention: `valuationMap` is −1 on a uniformizer, so a uniformizer goes to the inverse of arithmetic Frobenius and its inverse goes to arithmetic Frobenius. The file calls this the inverse-uniformizer convention of the native Artin map.
- These statements need L to carry its own local-field structure, a valuation extending that of K, and the unramified hypothesis; the Artin map itself is defined without them.
- The module docstring notes that no comparison of residue actions is assumed: unramifiedness of the small extension is derived.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `fdf703a292d4d502bec3f64b89395d1f249fd628d9244a08bcb91e92e4b2286c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
