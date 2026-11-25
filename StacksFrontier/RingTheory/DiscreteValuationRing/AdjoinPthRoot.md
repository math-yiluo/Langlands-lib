# Adjoining a prime-degree root to a DVR

Module `StacksFrontier.RingTheory.DiscreteValuationRing.AdjoinPthRoot`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with fraction field K, p a prime, and a ∈ A with residue class in κ(A) that is not a p-th power. The file shows that adjoining a p-th root of a produces a field extension and that the corresponding monogenic A-algebra is the integral closure.

In `Stacks.DiscreteValuationRing.AdjoinPthRoot`, `poly` and `polyK` are Xᵖ − a over A and K. `FieldExt` is the polynomial quotient over K, `alpha` is its distinguished root, and `ringExt` is the subalgebra B = A[α]. The file proves that α is integral, that its minimal polynomial over A is Xᵖ − a once Xᵖ − a is irreducible over K (`minpoly_alpha`), and that B is finite over A.

- `statement1_not_pth_power` excludes a p-th root of a in K, and `statement1_irreducible` deduces irreducibility of Xᵖ − a over K.
- `statement2_integralClosure` identifies B with the integral closure of A in `FieldExt` as a subalgebra.
- `statement3_dvr_weaklyUnramified` makes B a DVR and shows that every uniformizer of A maps to an irreducible element of B.

A p-th root in K would be integral over A and would reduce to a p-th root in κ(A). The power basis and irreducibility over κ(A) give a field as the closed fibre, so the base uniformizer generates the maximal ideal of the resulting DVR, which is integrally closed with fraction field `FieldExt`.

`FieldExt` is defined as a quotient, with its field structure supplied by the irreducibility proof. Weak unramifiedness here is preservation of uniformizers, or ramification index one. The hypothesis is on the residue of a and p may equal the residue characteristic.

The three numbered statements are Tag 09EX (1)–(3). The file also cites Tag 09E4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EX](https://stacks.math.columbia.edu/tag/09EX) | `statement1_not_pth_power` | (1) |
| [09EX](https://stacks.math.columbia.edu/tag/09EX) | `statement2_integralClosure` | (2) |
| [09EX](https://stacks.math.columbia.edu/tag/09EX) | `statement3_dvr_weaklyUnramified` | (3) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/AdjoinPthRoot.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 32 declarations of the source file 28 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.AdjoinPthRoot.alpha_pow_eq_algebraMap`, `Stacks.DiscreteValuationRing.AdjoinPthRoot.finrank_fieldExt`, `Stacks.DiscreteValuationRing.AdjoinPthRoot.isUnit_of_residue_not_pow`, `Stacks.DiscreteValuationRing.AdjoinPthRoot.natDegree_polyK`.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
