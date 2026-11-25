# Construction and uniqueness of the changed-uniformizer intertwiner

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let W be the completed unramified Witt ring `padicCompletedUnramifiedWittRing p`, φ its Witt-vector Frobenius, M the image in W⟦X⟧ of the multiplicative Lubin–Tate series of ℚ_p, and E the image of the standard Lubin–Tate series for the uniformizer changed by a unit u of ℤ_p. The file builds a power series H over W with zero constant term and prescribed linear coefficient such that E(H(X)) = φ(H)(M(X)), where φ(H) applies φ to each coefficient, and shows that such a solution is unique.

## Main definitions and results

- `PadicChangedUniformizerApproximation p u`: a structure holding a power series with zero constant term and linear coefficient `padicChangedUniformizerLinearCoefficient p u` (defined in an imported file).
- `padicChangedUniformizerApproximation p u n`: the n-th approximation. It starts from ε·X, ε the linear coefficient, and step n+1 adds c·X^(n+2) with c the correction coefficient of the defect-correction file.
- `padicChangedUniformizerIntertwiner p u`: the series whose m-th coefficient is the m-th coefficient of the m-th approximation. Simp lemmas give its coefficients and its linear coefficient ε; further lemmas give its zero constant term and admissibility for substitution.
- `padicChangedUniformizerIntertwiner_functionalEquation`: E ∘ H = φ(H) ∘ M, stated with the Lubin–Tate series mapped from the valuation subring of ℚ_p into W.
- `padicChangedUniformizerIntertwiner_unique`: two power series over W with zero constant term, equal linear coefficients, and both satisfying this functional equation are equal.

## Proofs

Coefficients of the approximations stabilize, so the intertwiner agrees with the (n+1)-st approximation up to degree n+2. The defect φ(H)(M) − E(H) vanishes in degree 0 because both series have zero constant term, in degree 1 by the Frobenius identity φ(ε) = ε·v for the linear coefficient (v the image of u), and in degree n+2 because the defect there depends only on coefficients up to degree n+2, where the correction has killed it. Uniqueness is by strong induction on the degree: the difference c of the m-th coefficients satisfies c = v⁻¹·p^(m−1)·φ(c), and the uniqueness of solutions of that equation, from an imported file, forces c = 0.

## Watch for

- Uniqueness is relative to a fixed linear coefficient; the statement says nothing about which linear coefficients admit solutions.
- The functional equation is stated over W and involves the Frobenius twist φ(H); it is not an equation over ℤ_p.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/IntertwinerConstruction.lean`: the Lean file is the source byte for byte (SHA-256 `98ddbea1650952f9d5e577dbb4bdf88197cc676f966ea47695d32bc82304deb9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
