# A right-unitary-invariant Schwartz majorant for complex matrix tests

`complexGodementUnitaryMajorant` bounds the absolute value of a rectangular complex Schwartz test by a real Schwartz function invariant under right multiplication by a unitary matrix.

The proof sends the matrix entries to Euclidean coordinates. The Schwartz seminorms of the transported test give rapid bounds there. A real radial bump equal to one on the unit ball supplies the input to the Library's dyadic Schwartz majorant construction. Each dilated bump depends only on the Euclidean norm, so the resulting majorant is constant on Euclidean norm spheres. Right unitary multiplication preserves the Euclidean norm because it preserves the sum of the squares in each row. Pullback along the linear equivalence gives the majorant with the operator matrix norm used for Godement tests.

This prepares joint absolute convergence for the open-cell comparison with a general Schwartz test. [Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 7.2 and equation (7.6)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
