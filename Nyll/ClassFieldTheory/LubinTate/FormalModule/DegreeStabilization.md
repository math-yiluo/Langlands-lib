# Finite-degree control of the Lubin–Tate intertwining defect

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix a local field K, an element π of its valuation ring, and two Lubin–Tate series e, ē for π (zero constant term, linear coefficient π, reduction X^q). For a power series H in finitely many variables Xᵢ, the intertwining defect `defect e ebar H` is e(H) − H(ē(X₁), …, ē(Xₙ)). The file shows that the defect in total degree at most m depends only on H through total degree m, and computes exactly how adding one monomial changes it. These are the facts used to build a full intertwiner from recursively corrected finite approximations.

## Main results

All in `LubinTate.SameUniformizer`.

- `truncTotal_succ_eq_iff_coeff_eq_degree_le`: two multivariable series have the same total-degree truncation below m + 1 iff their coefficients agree in every total degree at most m.
- `coeff_defect_eq_of_coeff_eq_degree_le`: if H and H′ have zero constant coefficient and agree in all total degrees at most m, their defects agree in all total degrees at most m.
- `coeff_defect_add_monomial_eq_of_degree_le`: if H has a prescribed linear term and d has total degree |d| ≥ 2, then replacing H by H + c·X^d leaves every defect coefficient of degree at most |d| unchanged except the one at d, which grows by π·(1 − π^(|d|−1))·c.
- `two_le_order_defect`: if H has a prescribed linear term (`HasLinearTerm H L`), its defect has no constant or linear terms.

## Proofs

Stability uses Mathlib's total-degree truncation, which commutes with substituting series of zero constant coefficient on both sides of the defect. For the monomial formula, ē(Xᵢ) agrees with π·Xᵢ up to order 2, so substituting into X^d gives π^|d|·X^d plus terms of higher degree; on the other side only the linear coefficient π of e contributes in degree |d|. A sequence of order estimates for differences of products of powers supplies the bounds. The order-2 statement reduces to the linear form, whose defect vanishes in degree at most 1.

## Watch for

- The variable type σ is finite, and the monomial formula requires |d| ≥ 2.
- No uniformizer hypothesis is used here; the factor 1 − π^(|d|−1) is a unit when π is a uniformizer, which the coefficient-equation file proves.
- e and ē have the same linear coefficient π.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`: the Lean file is the source byte for byte (SHA-256 `33415b004114f7be0be2eddd0bba7cdcc002e05f2ad93e591578c57cc3f4aa36`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
