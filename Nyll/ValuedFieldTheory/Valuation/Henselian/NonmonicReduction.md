# Constant reduction when the leading coefficient is not a unit

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.NonmonicReduction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file contains one step of the converse direction of the unique-extension criterion for henselian valuation rings: once all roots of an irreducible polynomial have the same value, a primitive polynomial whose leading coefficient is a nonunit has constant reduction. Here V is a valuation ring of K and B a valuation ring of L whose valuation extends that of V (`HasExtension`).

## Main result

- `primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit_of_roots_eq`: let Q ∈ V[X] be primitive with image p irreducible over K, let L be a splitting field of p over K, and suppose the leading coefficient of Q is not a unit and all roots of p in L have the same B-value. Then the reduction of Q has degree 0.

## Proof

By the Vieta estimate of the file on monic factor lifting (`not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit`), the constant coefficient a_0 must be a unit. Writing a_0 = ±lc(Q)·∏ roots with |lc(Q)| < 1 shows that the common value t of the roots exceeds 1. Then every coefficient of ∏(X − α) other than the constant one has strictly smaller B-value than the constant coefficient, so all a_j with j > 0 have value below 1 and reduce to zero.

## Points to watch

- Equality of the values of the roots is a hypothesis (`hrootsEq`), not something proved here; according to the module comment, no uniqueness of valuation extensions is used in this file.
- L must be a splitting field of p (`IsSplittingField`), and the valuation of B must extend that of V.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/NonmonicReduction.lean`: the Lean file is the source byte for byte (SHA-256 `70fd64fdf5b664eafbb33372336372c47efa0decf942c3d09270bd8ed1ceafc4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
