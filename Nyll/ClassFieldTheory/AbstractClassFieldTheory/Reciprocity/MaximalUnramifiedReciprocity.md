# Maximal-unramified reciprocity agrees with finite reciprocity

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a profinite group `G`, this file compares the maximal-unramified norm-residue symbol, a ↦ φ_K to the power v_K(a) for K-fixed elements a of `A`, with finite reciprocity on a finite unramified Galois extension L/K of a finite abstract field `K : FiniteAbstractField G`.

- `maximalUnramifiedNormResidueSymbol_finiteRestriction`: under `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`, restricting the maximal-unramified symbol of a to G(L/K) gives the inverse of `unramifiedReciprocityEquiv` applied to the norm class of a.
- `normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction`: under the class field axiom `hcf`, the finite norm-residue symbol `normResidueSymbol` of the norm class of a equals the class of that restriction in the abelianization of G(L/K).

The first follows from the generator computation `maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator`, using that unramified reciprocity sends Frobenius to the class of a prime element; the second combines it with the inverse relation between `normResidueSymbol` and `finiteReciprocityHom`.

Both statements require L/K to be unramified (`hUnramified : L.IsUnramified D`) and `G` compact, Hausdorff and totally disconnected. The symbols and fields are the library's own notions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/MaximalUnramifiedReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `b37167bfd578e01bb1a2129a6c973454dc83697f65b6bf415a4ed2725b1d754f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
