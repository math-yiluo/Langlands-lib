# Matrix descent from projective Galois lifts

Let `L/K` be an extension of fields in the same universe and let `I` be a
finite, decidable index type in `Type`. Suppose `P_s` is an invertible `I`-by-`I`
matrix over `L` for each `s ∈ Gal(L/K)` and
`P_s s(P_t) = c(s,t) P_(st)` with `c(s,t)` a unit scalar.
`SemilinearGaloisAction.ofProjectiveLifts` sends a matrix `X` to
`P_s s(X) P_s⁻¹`, where `s(X)` applies `s` to every entry. The factor-set
identity at the identity automorphism makes `P_1` scalar. The same identity
at `s,t`, together with invariance of conjugation under multiplying its
matrix by a unit scalar, gives the action law.

For finite Galois `L/K` and nonempty `I`, `matrixFixedCSA` packages the fixed
algebra of a semilinear action on these matrices as a finite-dimensional
central simple `K`-algebra. The splitting chart `matrixFixedSplittingChart`
supplied by finite Galois descent takes `l ⊗ a` to `l a` for fixed `a`.
`matrixFixedSplittingChart_action` uses that formula on pure tensors and
extends by additivity to recover the given action in the chart.

`relativeClass_ofProjectiveLifts` applies `BrauerComparison.descentClass_eq_of_lifts`
in this chart. The relative Brauer class in the convention of
`BrauerComparison.relativeClass` is represented by the two-cocycle `c`.
The construction extends the matrix descent calculation in
`BrauerComparison.RegularDescent` from the weighted regular matrices to
arbitrary supplied lifts with the scalar factor-set identity.
