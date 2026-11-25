# Finite norm quotients of the rational idele-class formation

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let ℚ̄ = `SeparableClosure ℚ` and G = Gal(ℚ̄/ℚ), acting on `rationalIdeleClassRepresentation`, the direct limit of idele class groups of finite extensions of ℚ inside ℚ̄. For closed subgroups L ≤ K of G, with K of finite index in G and L of finite index in K, let F and E be the library's abstract fixed fields of K and L. This file identifies the abstract finite norm subgroup and the finite norm quotient of the class formation with the norm range N(C_E) ⊆ C_F of the idele class norm N : C_E → C_F and the quotient C_F / N(C_E).

## Main results

- `rationalRelativeFixedFieldIdeleClassAdditiveType` and `rationalOrdinaryNormQuotientAdditiveType`: the additive groups C_E and C_F / N(C_E), with the instances on F and E built in.
- `rationalAbstractRelativeFixedFieldIdeleClassEquivFixed`: C_E is additively isomorphic to the L-fixed part of the representation. It needs no normality.
- `rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm`: when L is normal in K (so E/F is Galois), the relative norm of the class formation from the L-fixed part to the K-fixed part corresponds to the idele class norm C_E → C_F.
- `map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete`: under the K-fixed-part isomorphism, `finiteNormSubgroup` is exactly the range of the idele class norm.
- `rationalFiniteNormQuotientEquivIdeleClassNormQuotient`: `FiniteNormQuotient` is isomorphic to C_F / N(C_E). The simp lemma `..._finiteNormClass` says it sends the class of a fixed element to the class of the corresponding idele class.
- General helpers: `quotientAddEquivOfEquivMapEq` (an additive isomorphism that matches two subgroups descends to the quotients) and `additiveQuotientEquiv` ((`Additive` G) ⧸ H ≃+ `Additive` (G ⧸ H)).

## Proofs

The norm compatibility goes through the relative idele class groups of ℚ ⊆ F ⊆ E. It uses the tower and base-change isomorphisms of the imported files and the comparison of their cohomological norm with the ordinary idele class norm. The statement about subgroups follows from the norm compatibility by a general lemma on images of ranges under isomorphisms.

## Points to watch

- Everything is over the base field ℚ and its separable closure, not over a general number field.
- F and E are the library's abstract fixed fields of closed subgroups. `FiniteNormQuotient` and `finiteNormSubgroup` belong to the library's abstract class formation.
- The finite-index conditions are instance arguments written as finiteness of quotients by `extensionSubgroup`. Normality of L in K is an explicit hypothesis for the norm statements.
- The statements bind the needed instances (finite dimension, `NumberField`, `IsGalois`) with `let` inside the statement. A local instance gives C_F its quotient commutative group structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `3d8433597d8450ec8eb9a25be21362aa29ab269420925373d2f0753ca169254b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
