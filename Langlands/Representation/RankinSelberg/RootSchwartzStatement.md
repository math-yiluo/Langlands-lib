# Schwartz tests in the full root-coordinate space

`Langlands.RankinSelberg.RootSchwartzAssemblyStatement F n` concerns a
Hausdorff field with a topology making addition and multiplication continuous.
It retains the field universe and every natural number `n`, so the resulting
coordinate space has positive dimension `n + 1`, including dimension one.
No local compactness or continuity of field inversion is assumed.

For any two Schwartz–Bruhat functions `φ, φ'` on `Fin n → F`, any
Schwartz–Bruhat function `Φ` on `Fin (n + 1) → F`, and any invertible matrix
`k` of size `n + 1`, the statement asserts existence of a Schwartz–Bruhat
function `Ψ` on the full coordinate space with the exact values

\[
\Psi(x)=\phi(x_0,\ldots,x_{n-1})\,
        \phi'(x_0,\ldots,x_{n-1})\,
        \Phi(x_n\,\operatorname{lastRow}(k)).
\]

Here Schwartz–Bruhat means locally constant with compact topological support,
as defined in `HarmonicAnalysis.Basic`. The formula holds at every field
vector, including vectors with zero coordinates. The matrix is arbitrary
invertible; it need not belong to an integral or compact subgroup.

This is an internal elementary adapter for the published
`CoefficientTorusExpansion` and `RootCoordinateChangeStatement`. The two
coefficient expansions supply the tests in the first `n` root coordinates.
The last-row identity in the root-coordinate statement supplies the argument
`x_n • lastRow k` of the remaining test. This adapter states precisely that
their product is a test on the full field vector space, as required in the
torus Mellin reduction. It does not construct coefficient expansions or assert
any integral identity, convergence, rational continuation, denominator bound,
or normalized generator.

The internal provenance is elementary topology and linear algebra, rather
than a separately attributed literature theorem. Local constancy is preserved
by composition with the continuous coordinate and scalar-multiplication maps
and by products. Invertibility gives a nonzero entry `v_j` in the last row.
The support of the displayed product is contained in the compact image of
`tsupport φ × tsupport Φ` under
`(y,z) ↦ Fin.snoc y (z_j / v_j)`. This map uses multiplication by the fixed
inverse of `v_j`, hence does not require continuity of inversion. The
Hausdorff hypothesis makes the containing compact set closed and therefore
also contains the topological support. At `n = 0`, the first coordinate space
is a singleton and the same argument applies.

The Lean file defines the proposition target; it does not prove it.
