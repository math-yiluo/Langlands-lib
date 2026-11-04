# Character-linear kernels for the actual triangular quotient series

This internal construction works over an arbitrary field `k : Type u` and
positive matrix size `N`, with the actual triangular homomorphism `j`, an
arbitrary commutative group scheme `D`, and an actual diagonal factorization
`q ≫ d = j ≫ blockLimitHom`. It makes no smoothness, connectedness,
reducedness, or torsion-free character assumption.

`seriesRatioCharacter d hN t` gives the actual diagonal ratio for the row
`t % N` and column `t % N + t / N + 1` whenever that column is in range.
For an out-of-range column the adjacent subgroup terms repeat and the
character is zero. `seriesConjugation j t` is the existing actual ambient
conjugation on the enumerated full coordinate subgroup at index `t`.

`seriesCoordinate_equivariant` proves that the actual map
`seriesCoordinate` intertwines this action with the weight action of
`seriesRatioCharacter`, after `q`, on every relative test scheme.
For a genuine coordinate it applies `filtrationCoordinate_equivariant`.
For a repeated term the coordinate is the zero homomorphism, so both sides
are the identity point of the additive group. The theorem holds at every
natural index, beyond as well as within the finite segment ending at `N*N`.

`seriesComparison_isCharacterLinearKernel` takes actual quotient terms
`A = H/F_t` and `B = H/F_(t+1)` and an fpqc structural map
`r : B → D` satisfying `B.hom ≫ r = q`. It proves the unchanged predicate
`LinearKernelTower.IsCharacterLinearKernel D r` for the actual comparison
`B → A`. Its kernel is the full scheme kernel, including finite or
nonreduced possibilities. The theorem assumes affine, locally finite type
`H`, and retains `AffineHomImageStatement` as an explicit premise.
Quotient existence is retained through the supplied `QuotientTerm` objects;
the fpqc conditions on `r` are explicit.

The proof equips the current actual subgroup with its known affine and
finite type geometry and monic inclusion, uses the full internal kernel
identity for `seriesCoordinate`, and supplies the preceding character
equivariance to `QuotientTerm.isCharacterLinearKernel_of_coordinate`.
That construction obtains a closed additive embedding from the explicit
image premise and descends actual conjugation by independent fpqc local
lifts. The factorization of `r` identifies the lifted acting point with
its original `q` value. No assertion of global lifting on arbitrary tests
is used.

The provenance is internal and derives from the explicit series, actual
coordinate character calculation and full-kernel fpqc descent. This module
does not prove image or quotient existence, construct the remaining
structural maps `r`, assemble the finite quotient tower, or prove splitting.
Size zero is left to the endpoint assembly and is not covered by `hN`.
