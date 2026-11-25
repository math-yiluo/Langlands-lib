# Completed p-adic Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedLevel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let A = Frac(W(F̄_p)) be the completed maximal unramified extension of ℚ_p, with valuation ring the Witt ring W. The file base-changes the n-th standard primitive Lubin–Tate polynomial of ℚ_p (uniformizer p) to A and defines the completed level as its splitting field over A. It equips this field with a complete discrete valuation whose valuation ring is the integral closure of W, picks a primitive root, and sets up convergent evaluation of power series over W at topologically nilpotent elements of that valuation ring.

## Main definitions and results

- `padicCompletedPrimitivePolynomialInteger`, `padicCompletedPrimitivePolynomial`: the primitive polynomial over W and over A; monic, of degree (p − 1)·p^n, separable over A, and weakly Eisenstein at the maximal ideal of W.
- `padicCompletedLevelField p n`: the splitting field over A; instances: field, A-algebra, finite-dimensional, Galois. The polynomial splits there and its roots generate it.
- `padicCompletedPrimitiveRoot`: a chosen root (`Polynomial.rootOfSplits`), integral over W.
- `padicCompletedLevelCompleteDVF`: a complete discrete valuation on the level, chosen from `padicCompletedLevelCompleteDVFData_exists`; it extends the valuation of A, its valuation ring is the integral closure of W, and the fundamental identity e·f = degree holds.
- `padicCompletedPrimitiveRootInteger`: the root in that valuation ring; it lies in the maximal ideal (`..._mem_maximalIdeal`) and is an admissible evaluation point (`..._hasEval`).
- `padicCompletedLevelWittCoefficientHom`: the map from W to the valuation ring, continuous for the discrete topology on W.
- `padicCompletedLevelPowerSeriesEval p n x hx`: evaluation of power series over W at an admissible x, a ring map with simp lemmas for X, constants and polynomials. It is continuous, sends series with zero constant term to admissible points, and commutes with substitution: for a admitting substitution (`PowerSeries.HasSubst a`), f(a(X)) evaluated at x equals f evaluated at a(x) (`..._subst`); this statement takes the admissibility of a(x) as an explicit argument `haEval`, which `padicCompletedLevelPowerSeriesEval_hasEval` supplies.

## Proofs

The maximal-ideal membership comes from the weak Eisenstein property: a power of the root lies in the extended maximal ideal of W. The valuation is obtained from a general existence theorem for integral closures of complete discrete valuation rings in finite separable extensions.

## Watch for

- The primitive root and the valuation on the level field are chosen by `Classical.choose`, not given explicitly.
- Evaluation uses local instances of this file: the discrete uniformity on W and the maximal-ideal adic topology on the valuation ring, which is complete and Hausdorff.
- The level is the splitting field over A, not over ℚ_p.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedLevel.lean`: the Lean file is the source byte for byte (SHA-256 `cefc22cd0ac7373523b323f210e246fccea72db5afd5b6bd9bd24e23a7523955`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
