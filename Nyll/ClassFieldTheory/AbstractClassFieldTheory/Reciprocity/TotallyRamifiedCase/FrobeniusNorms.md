# Frobenius actions and norms in the auxiliary totally ramified tower

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusNorms`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix, in abstract class field theory over a compact Hausdorff group `G`, a finite Galois totally ramified extension L/K with `K : FiniteResidueAbstractField D`, an automorphism q ∈ G(L/K), its chosen degree-one Frobenius lift σ̃ with fixed field Σ, and the auxiliary finite Galois extension M ⊇ L, Σ of K with maximal unramified subextension M₀ over K. This file defines the image of σ̃ in G(M/K) and proves the identities on actions and norms used to build the fixed element in the reciprocity argument.

## Definitions and results

- `abstractReciprocityTotallyRamifiedFrobeniusInM`: the image t of σ̃ in G(M/K), well defined because the inertia of L (the elements of L of trivial degree, `D.extensionInertiaWithin K.field L.field L.below`) lies in the subgroup of M. It restricts to q on L (`…FrobeniusInM_restriction`).
- `abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction`: the element g of G(M/M₀) that the restriction equivalence sends to q (`abstractReciprocityTotallyRamifiedLowerGenerator`; q is any element here, so g need not generate), viewed in G(M/K), also restricts to q on L.
- `abstractReciprocityTotallyRamified_generator_commutes_frobenius`: g and t commute, since they have the same restriction to L and M lies in the maximal unramified extension of L.
- `abstractReciprocityTotallyRamified_frobenius_fixes_sigma`: t fixes every element of A_Σ, viewed in A_M.
- `abstractReciprocityTotallyRamified_actions_agree_on_L`: g and t act equally on elements of A_L, viewed in A_M.
- `abstractReciprocity_totallyRamified_relativeNorm_L`: the norm from M to M₀, restricted to A_L, is the norm from L to K, both read among the M₀-fixed elements.
- `abstractReciprocity_totallyRamified_relativeNorm_sigma`: likewise the norm from M to M₀ on A_Σ is the norm from Σ to K; this uses that Σ/K is totally ramified, its residue degree being the exponent 1 of σ̃, and needs `G` totally disconnected.

## Points to watch

The element g and the restriction equivalence come from the imported file `RestrictionEquiv`; the norm identities rest on `abstractReciprocity_relativeNorm_fixedFieldInclusion`, which is not in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean`: the Lean file is the source byte for byte (SHA-256 `4c3bf74309d9fb5e804cbe0406cb8398956521cbc19543a7595e2a24363e8a17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
