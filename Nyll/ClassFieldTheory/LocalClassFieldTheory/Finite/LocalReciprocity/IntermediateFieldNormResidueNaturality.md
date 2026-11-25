# Restriction naturality of the local norm-residue symbol for intermediate fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` and finite abelian extensions `E ≤ F` given as intermediate fields of `SeparableClosure K`, this file shows that the concrete norm-residue symbol for `F`, followed by restriction `Gal(F/K) → Gal(E/K)`, is the symbol for `E`. It deduces the corresponding statement for the local Artin map of a nonarchimedean local field.

## Main definitions and results

- `embeddedBaseNormClass`: for an embedding `i : L →ₐ[K] SeparableClosure K` of a finite Galois `L`, the class of `a ∈ Kˣ` in the abstract finite norm quotient.
- `concreteNormResidueSymbolOfEmbedding_eq_abstract`: the concrete norm-residue symbol of `a` for `L` (built from degree data `D`, valuation data `v` and a class field axiom `hcf`) is the abstract symbol `D.normResidueSymbol` of that class, carried through the map on abelianizations induced by the canonical isomorphism of the abstract quotient with `Gal(L/K)`.
- `concreteNormResidueAutomorphism_restrict`: for `E ≤ F` finite abelian over `K` and `a ∈ Kˣ`, restricting the symbol of `a` for `F` to `E` (via `intermediateFieldRestrictNormalHom`) gives the symbol for `E`, for the same `D`, `v`, `hcf`.
- `localArtinAutomorphism_restrict`: the same for `localArtinMonoidHom` of a nonarchimedean local field, using the canonical local data `localResidueDatum`, `localHenselianValuation` and `separableClosureUnits_isClassFormation`.

## Proof

The abstract norm-restriction naturality of the class formation is applied with trivial base extension, where the relative norm is the identity; private lemmas check that the abstract restriction of quotient classes corresponds to restriction of the actual automorphisms.

## Points to watch

- The general statements carry the class field axiom as a hypothesis `hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K)`; only `localArtinAutomorphism_restrict` supplies a specific one.
- The extensions are literal intermediate fields of the chosen separable closure, so that the vertical map is honest restriction; arbitrary towers are treated elsewhere.
- The fields `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `8c3eaabdd0a4a8ea39cb73d6573a0f08bcac1b612ffe45d4d068cec661ee9dd5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
