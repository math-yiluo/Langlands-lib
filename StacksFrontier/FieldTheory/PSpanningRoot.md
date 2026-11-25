# Fields spanned by powers of one element

Module `StacksFrontier.FieldTheory.PSpanningRoot`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

When a field K of prime characteristic p is spanned over Kᵖ by 1, t, …, t^(p−1) and t has no p-th root in K, the inseparability in a finite extension can be accounted for by adjoining an iterated p-th root of t.

For a commutative ring, `IsPSpannedBy p t` requires every element to be a sum of the powers tⁱ for 0 ≤ i < p with coefficients that are p-th powers. In characteristic p over the prime field this is the spanning condition for a singleton p-basis. The lemma `exists_fin_repr_of_sum` reduces arbitrary exponents to this range using remainders modulo p. `IsPSpannedBy.map_ringEquiv` transports the property along ring isomorphisms, and `IsPSpannedBy.algebraMap_fractionRing` passes it from a domain to its fraction field for p ≠ 0.

`IsPSpannedBy.of_adjoin_root` transfers the spanning property from t in K to ρ in an extension generated polynomially by ρ when ρ^(pⁿ) is the image of t. If F is p-spanned by t and t has no p-th root in an algebraic extension M/F, `Algebra.IsSeparable.of_isPSpannedBy` shows that M/F is separable. Its proof uses independence of powers of t over Mᵖ to rule out an inseparable minimal polynomial.

For K of characteristic p, t in K not a p-th power, and y in any extension of K with y^(pʲ) = t, `minpoly_eq_X_pow_sub_C_of_pow_eq` shows that the minimal polynomial of y over K is X^(pʲ) − t; this needs no spanning hypothesis.

For finite M/K under the opening hypotheses, `exists_pow_eq_minpoly_eq_and_isSeparable_adjoin` gives n and ρ in M with ρ^(pⁿ) = t, minimal polynomial X^(pⁿ) − t over K, and M separable over K(ρ). The proof uses `minpoly_eq_X_pow_sub_C_of_pow_eq` to bound n by the extension degree and chooses the largest possible n, so that ρ has no p-th root in M.

The file cites Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/PSpanningRoot.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
