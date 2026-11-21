# Rational matrices in adelic conjugates of compact sets

`Langlands.Global.AdelicGL.AdelicGLCompactConjugateCountingStatement` concerns
`GL_n` over a number field `F`. Fix a compact set `S` in `GL_n(𝔸_F)` and a
finite adelic point `b`. For `a ∈ GL_n(F∞)`, let `x = pair F n a b` and put
`P_x = {g ∈ GL_n(F) | rational F n g ∈ x S x⁻¹}`. The theorem
`adelicGLCompactConjugateCounting` proves that `P_x` is finite and that

\[
\# P_x \le B\, H(a)^{2d},\qquad
H(a)=\texttt{infiniteAdelicHilbertNorm}\ F\ n\ a,\quad
d=\dim_{\mathbb R}(\texttt{ArchimedeanMatrix}\ F\ n).
\]

The nonnegative real constant `B` may depend on `S` and `b`, but not on `a`.
The statement uses the operator norm on the archimedean matrix coordinate for
packing and the Library's Hilbert height in the final bound.

## Implemented proof

Embed the additive group of rational matrices entrywise in the product of the
mixed archimedean matrix space and the finite adelic matrix space. Each entry
can be recovered in the adele ring by a continuous projection followed by
combining its two coordinates. The diagonal map on rational matrices is
injective by injectivity of the scalar diagonal. Requiring each recovered
entry to lie in the open isolating neighborhood for the principal adeles
isolates the zero matrix in the range. Thus the additive diagonal matrix
subgroup is discrete.

At the fixed finite coordinate `b`, finite matrix coordinates of the points
of `x S x⁻¹` lie in the compact image of `S` under `s ↦ (b · finite(s) · b⁻¹).val`.
For the first coordinate, the operator norm of the archimedean matrix of
`x s x⁻¹` is at most the norm of the matrix of `s` times the square of the
archimedean matrix height of `a`. This follows by submultiplicativity and the
bounds on the matrix norms of `a` and `a⁻¹`. Compactness bounds the norm for
`s ∈ S`; `archimedeanMatrixHilbertComparison` then bounds the first coordinate
by `D H(a)^2` for some `D ≥ 0` independent of `a`.

The image of `P_x` under the additive diagonal map on the underlying matrices
therefore lies in the slice counted by `discreteProductSubgroupCounting`, at
radius `D H(a)^2`. The map on `P_x` is injective since a matrix unit is
determined by its matrix value. The generic estimate gives finiteness and a
bound by a constant times `(1 + D H(a)^2)^d`. Since `H(a) ≥ 1`, this implies
the displayed bound with a constant independent of `a`.

## Provenance and scope

This is a derived specialization of compact-slice counting, using the
published principal-adele isolating set and matrix height comparison. Its
purpose is the polynomial growth step in constructing forms from cuspidal
Hilbert summands, in the direction of Getz–Hahn, *An Introduction to
Automorphic Representations*, Springer GTM 300 (2024), Theorem 9.7.3,
pp. 265–267 (PDF pp. 277–279). The counting inequality is an auxiliary
estimate for the Library's route, not the statement of that theorem. Passing
from principal-point counts to positive-central subgroup Haar mass and then
to growth of quotient representatives requires separate comparisons.
