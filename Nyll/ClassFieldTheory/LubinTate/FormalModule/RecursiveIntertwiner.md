# Existence and uniqueness of Lubin–Tate intertwiners

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file proves the central lemma of Lubin–Tate theory for a fixed uniformizer. Let π be a uniformizer of a local field K, e and ē Lubin–Tate series for π, σ a finite set of variables and L : σ → valuation ring a linear form. Then there is exactly one power series H in the variables Xᵢ, i ∈ σ, with zero constant coefficient, linear term Σᵢ Lᵢ·Xᵢ (`HasLinearTerm H L`) and e(H) = H(ē(Xᵢ)ᵢ). The series is built degree by degree from the monomial corrections of the earlier files.

## Main definitions

In `LubinTate.SameUniformizer`:

- `IntertwinerApproximationData L`: series together with a proof that their linear term is L.
- `intertwinerDegreeIndexList m`: a list of all multi-degrees of total degree m.
- `intertwinerCorrectionStep`, `intertwinerCorrectList`, `intertwinerCorrectDegree`: one monomial correction, a list of them applied in order, and the correction of every monomial of one total degree m ≥ 2.
- `intertwinerApproximation hpi e ebar L n`: stage 0 is the linear form; stage n + 1 corrects total degree n + 2.
- `recursiveIntertwiner hpi e ebar L`: the series whose coefficient at d is that of stage |d| − 1.

## Main results

- `linearForm_hasLinearTerm`, `intertwinerApproximation_hasLinearTerm`, `intertwinerApproximation_zero`: basic properties of the stages.
- `coeff_intertwinerApproximation_succ_eq_of_degree_lt`, `coeff_intertwinerApproximation_eq_of_le`: coefficients of total degree below n + 2 do not change after stage n.
- `coeff_defect_intertwinerApproximation_succ_eq_zero`: stage n + 1 has zero defect in total degree n + 2.
- `coeff_recursiveIntertwiner_eq_intertwinerApproximation`: through degree n + 1 the limit agrees with stage n.
- `recursiveIntertwiner_hasLinearTerm`, `coeff_defect_recursiveIntertwiner_eq_zero`, `recursiveIntertwiner_intertwines`: the limit has linear term L and solves the equation.
- `eq_recursiveIntertwiner_of_hasLinearTerm_of_intertwines`, `eq_of_hasLinearTerm_of_intertwines`: any solution with linear term L is the recursive one; two such solutions are equal.
- `existsUnique_intertwiner`: existence and uniqueness.

## Proofs

Within one total degree, a correction at d changes only the defect coefficient at d, so correcting along a duplicate-free list clears the whole degree; lower coefficients never move. The defect of the limit vanishes in each degree because, by degree stabilization, it agrees there with the defect of a finite stage. Uniqueness is by strong induction on total degree: replace the degree-m coefficients of a solution H by those of the recursive solution R; the defect formula gives π·(1 − π^(m−1))·(R_d − H_d) = 0, and since π ≠ 0 and 1 − π^(m−1) is a unit, R_d = H_d.

## Watch for

- e and ē must have the same uniformizer π; series for different uniformizers are not treated here.
- The variable set σ is a `Fintype`; the statement is for multivariable series in general, of which the one-variable endomorphisms and the two-variable formal group law are special cases.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`: the Lean file is the source byte for byte (SHA-256 `ce7ccbe1cab6e6e22ca1a01009fca89957240a8984f49719f16d907bef8741d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
