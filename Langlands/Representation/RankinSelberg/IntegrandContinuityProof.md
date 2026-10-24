# Proof of continuity of the equal-rank quotient integrand

`Langlands.RankinSelberg.equalRankIntegrandContinuous` proves
`EqualRankIntegrandContinuousStatement` for independent field and
representation universes, retaining the given topology and continuous
real absolute value. Both representations need only be smooth. In
particular the theorem permits zero functionals and reducible
representations.

The proof uses `modelMap_surjective` to represent each coefficient-model
vector by a vector in its representation. The theorem
`matrixCoefficient_isLocallyConstant` then gives local constancy and hence
continuity of each coefficient function. This argument applies to both the
standard and inverse-standard functionals without imposing a topology on
either representation space.

The row map is continuous entry by entry, so composition with the locally
constant Schwartz–Bruhat test is continuous. The determinant absolute value
is continuous by continuity of the determinant and the assumed continuity
of `abv`. Since the determinant of every invertible matrix is nonzero, its
absolute value is strictly positive. Its complex image therefore lies in
the slit plane, where complex power with the fixed exponent `s` is
continuous. Multiplying these continuous functions gives continuity of the
integrand before descent.

Finally, `leftQuotient_isOpenQuotientMap` supplies the universal property
of the actual left-unipotent quotient topology. The composite of the
published `equalRankIntegrand` with the quotient projection is definitionally
the continuous group integrand just constructed. The quotient-map
continuity equivalence proves the target.

This is an internal consequence of the imported matrix-coefficient and
quotient definitions and standard continuity results. It establishes the
measurability prerequisite for Borel quotient integration, but asserts no
convergence, rational continuation, or integral interchange.
