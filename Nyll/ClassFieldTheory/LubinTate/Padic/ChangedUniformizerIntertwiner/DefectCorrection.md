# Degreewise correction of the changed-uniformizer defect

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let W be the completed unramified Witt ring `padicCompletedUnramifiedWittRing p` (Witt vectors of an algebraic closure of 𝔽_p), φ its Witt-vector Frobenius, M the completed multiplicative Lubin–Tate series over W and, for a unit u of ℤ_p with image v in W, E = v·p·X + X^p the changed-standard series. For a power series H over W, the file studies the defect φ(H)(M(X)) − E(H(X)), where φ(H) applies φ to every coefficient. It shows that the defect is divisible by p, computes how adding a monomial changes it, and constructs the coefficient that kills it in a given degree.

## Main definitions and results

- `padicChangedUniformizerDefect p u H`: the defect above.
- `padicChangedUniformizerDefect_map_constantCoeff`, `padicChangedUniformizerDefect_coeff_mem_span_p`: if H has zero constant term, the defect reduces to 0 modulo p, so every coefficient lies in the ideal (p).
- `padicChangedUniformizerNormalizedDefect`: a chosen quotient of the degree-m defect coefficient by p.
- `padicCompletedMultiplicativeSeries_order`, `padicCompletedMultiplicativeSeries_coeff_pow_self`: M has order 1, and the X^m-coefficient of M^m is p^m.
- `padicChangedUniformizerDefect_coeff_add_monomial`: for H with zero constant term and m ≥ 2, replacing H by H + c·X^m changes the degree-m defect coefficient by p^m·φ(c) − v·p·c.
- `padicChangedUniformizerCorrectionCoefficient`: for m ≥ 2, the coefficient c with c = v⁻¹·b + v⁻¹·p^(m−1)·φ(c), b the normalized defect, chosen from `existsUnique_padicChangedUniformizerCoefficient` of an imported file. `..._spec` records this equation, and `..._kills_defect` shows that H + c·X^m has zero defect in degree m.
- `padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le`: for series with zero constant term, the degree-m defect coefficient depends only on the coefficients of H up to degree m. The general helper `powerSeries_truncTotal_succ_eq_of_coeff_eq_le` turns agreement of coefficients up to degree m into equality of total truncations.

## Proofs

Modulo p, M and E both reduce to X^p (lemmas of imported files), and coefficientwise Frobenius after expansion by p is the p-th power, so both terms of the defect become H̄(X)^p. The monomial formula rests on (H + c·X^m)^p and H^p agreeing in degree m when H has zero constant term and m ≥ 2, shown by a geometric-sum factorization and order estimates.

## Watch for

- The normalized defect takes the hypothesis "constant term of H is 0" as an argument, in every degree m; the correction coefficient takes this hypothesis and "m ≥ 2" as arguments.
- Each correction kills the defect in one degree only; assembling a full intertwiner is not done in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/DefectCorrection.lean`: the Lean file is the source byte for byte (SHA-256 `f8185bfd9912c7aaf07dd5733050feb7f1b07c9ce737be8a3e393e4de0c12e04`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
