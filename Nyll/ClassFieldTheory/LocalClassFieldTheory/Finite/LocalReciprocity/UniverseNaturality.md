# Functoriality of the Artin map in any universes

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves the two functoriality properties of the universe-polymorphic abelian local Artin map `LocalClassFieldTheory.Universe.abelianLocalArtinMap`: compatibility with restriction in a tower and with norms under base change. Each is reduced to the native statement for small copies `Shrink.{0}` of all fields involved, with the algebra maps of the tower transported together.

## Main results

- `abelianLocalArtinMonoidHom_restrict_tower`: for a nonarchimedean local field K : Type u and a tower K ⊆ E ⊆ L (E : Type v, L : Type w) with E/K and L/K finite abelian Galois, restricting the Artin image of a from L to E gives the Artin image of a for E/K.
- `abelianLocalArtinMap_restrict`: the same for the continuous maps, for intermediate fields E ≤ F of `SeparableClosure K` that are finite abelian over K, via `intermediateFieldRestrictContinuous`.
- `abelianLocalArtinMonoidHom_norm_restriction`: let K' : Type v be a finite separable extension of K that is itself a nonarchimedean local field whose valuation extends that of K, L/K finite abelian, L'/K' finite abelian, with L → L' compatible with K → K'. Then for a ∈ K'^×, the Artin image of a for L'/K', viewed as a K-automorphism and restricted to L, equals the Artin image, for L/K, of the norm of a from K' to K.

Two helper results support the proofs: `shrink_valuationHasExtension` (an extension of valuations survives shrinking both fields) and `normUnits_shrink` (the field norm commutes with the shrinking unit equivalences).

## Caveats

In the norm statement, K' needs its own topology, `ValuativeRel` and `IsNonarchimedeanLocalField` instance and `Valuation.HasExtension`; L and L' need no local-field structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `24ad4e1218726715eff9c24113a65171539bcd03ab2e52553ad60aa99044125c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
