# Geometric trace comparison from degree lines and Tate determinant norms

This module defines `GeometricDegreeTraceReductionStatement` and proves it with
`geometricDegreeTraceReduction`. The proposition is

`EndomorphismDegreeLinePolynomialStatement.{u} → IsogenyDegreeTateDeterminantNormStatement.{u} → GeometricEndomorphismTraceComparisonStatement.{u}`.

Both premises and the conclusion are existing Library propositions, at their
full common universe scope. The first premise supplies a rational function on
actual endomorphisms, equal to the native finite-flat rank on isogenies, whose
restriction to each natural-number line is a rational polynomial. The second
premise compares that rank's prime-adic norm with the determinant of the actual
rational Tate map on isogenies and makes that determinant zero off isogenies.
This module proves a conditional reduction; it does not prove either premise.

Fix an actual abelian scheme over an algebraically closed characteristic-zero
field and an integral endomorphism `f`. Choose its relative dimension `g` and
the rational function `δ` supplied by the first premise. Choose one rational
polynomial `P` with `P(n) = δ(n • 1 - f)` for every natural number `n`. These
choices precede the choice of prime.

At each prime `p`, the published geometric Tate rank theorem supplies a basis
of the actual rational Tate module indexed by `Fin (2 * g)`. Compose the
actual rational endomorphism action with that matrix basis to form `ρ`.
As in `IsogenyDegreeTateDeterminantCharZeroReduction`, the line premise, the
native-rank composition formula for isogenies, and the determinant norm premise
give `DegreeData ρ δ IsIsogeny`. Its published theorem `DegreeData.det_eq`
therefore identifies `δ(β)` with `det(ρ(β))` for every actual endomorphism `β`.

Apply this identity to `n • 1 - f`. The characteristic-polynomial evaluation
formula then identifies `P.map (algebraMap ℚ ℚ_[p])` with `(ρ f).charpoly`:
the two polynomials agree on every natural-number scalar in the
characteristic-zero field `ℚ_[p]`, an infinite set. Trace is the negative next
coefficient of the characteristic polynomial, and next coefficients commute
with this injective coefficient map. Consequently `-P.nextCoeff` maps to the
actual integral Tate trace at every prime. The matrix trace formula includes
the empty matrix, so this argument also covers relative dimension zero.

Finally `GeometricTrace.comparison_of_integral` extends these common rational
traces to the rationalized endomorphism ring and proves all clauses of the
unchanged geometric comparison target, including finite dimensionality and
the rank formula.

The provenance is an internal composition of the named Library reductions,
the algebraic degree-determinant theorem, and the ordinary characteristic
polynomial and trace identities. No additional geometric polynomiality or
determinant norm assertion is introduced.
