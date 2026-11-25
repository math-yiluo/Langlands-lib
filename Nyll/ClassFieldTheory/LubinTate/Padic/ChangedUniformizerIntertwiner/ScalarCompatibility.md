# The changed-uniformizer intertwiner and scalar endomorphisms

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over the completed unramified Witt ring W of ℚ_p, let H be the changed-uniformizer intertwiner for a unit u of ℤ_p: the power series with zero constant term and linear coefficient `padicChangedUniformizerLinearCoefficient p u` solving E(H(X)) = φ(H)(M(X)), where M is the multiplicative Lubin–Tate series, E the changed standard series and φ(H) the series with Witt-vector Frobenius applied to each coefficient. The file shows that H intertwines the scalar endomorphisms of the two formal groups and computes φ(H).

## Main results

- `padicChangedUniformizerIntertwiner_endomorphism`: for every a in ℤ_p, H([a]_M(X)) = [a]_E(H(X)), where [a]_M is `padicCompletedMultiplicativeScalarEndomorphism p a` and [a]_E is `padicCompletedChangedStandardScalarEndomorphism p u a`.
- `padicChangedUniformizerIntertwiner_frobenius`: φ(H) = H ∘ [u]_M, that is, Frobenius on the coefficients of H is precomposition with the multiplicative endomorphism of u.

## Proofs

Both results use the uniqueness theorem for the intertwiner: a solution of the functional equation with zero constant term is determined by its linear coefficient. For the first, both H ∘ [a]_M and [a]_E ∘ H solve it: this uses that [a]_M commutes with M and [a]_E with E, that φ fixes these endomorphisms coefficientwise, and that both have linear coefficient ε·a, ε the linear coefficient of H. For the second, φ(H) solves the equation because φ fixes M and E, its linear coefficient is φ(ε) = ε·v with v the image of u, and H ∘ [u]_M has the same linear coefficient.

The comment on the first theorem says it is the formal-series compatibility used in the cyclotomic action formula for the Lubin–Tate character.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/ScalarCompatibility.lean`: the Lean file is the source byte for byte (SHA-256 `41bf74b6d2848eeb1e31d1f29875ba1da3183e1d65737cdac26ad8200848a576`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
