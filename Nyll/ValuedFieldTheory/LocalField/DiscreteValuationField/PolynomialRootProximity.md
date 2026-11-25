# A root-proximity estimate over a discrete valuation ring

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `R` be a discrete valuation ring with additive valuation `v = IsDiscreteValuationRing.addVal R`, with values in `ℕ∞`. The file shows that a split monic polynomial has a root close to any point where its value is small, measured against the derivative at that root.

`Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivative`: let `p` be a monic polynomial over `R` of positive degree that splits over `R`. For every `x` in `R` there is a root `y` of `p` (an element of `p.roots`) with

`v(p(x)) ≤ v(x − y) + v(p′(y))`.

The proof takes a root `y` with `v(x − y)` maximal. For every other root `z` the ultrametric inequality gives `v(x − z) ≤ v(y − z)`, and the product of the factors `y − z` over the remaining roots is `p′(y)`. A private helper lemma compares the valuations of two such products factor by factor.

Watch for:

- The polynomial must split over `R` itself, not over its fraction field.
- Repeated roots are allowed. At a multiple root `p′(y) = 0`, the right-hand side is `∞` and the bound says nothing.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean`: the Lean file is the source byte for byte (SHA-256 `4f6055898ccd8ba09406459eafb4c76d5a62d289d1a27d7c21924107c62a62fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
