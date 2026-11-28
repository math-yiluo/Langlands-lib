# Polynomial rank bounds for compact averaging at infinity

For a number field `F` and a natural rank `n`, let `G` be the actual archimedean general linear group and `K` its standard compact subgroup. The latter is a product of real orthogonal and complex unitary groups. Its matrix in mixed archimedean coordinates is `compactMatrix F n`. Real coordinates on this finite-dimensional real matrix algebra are taken in `Module.finBasis`. The restriction to `K` of a complex polynomial in these coordinates is `compactCoordinatePolynomial`.

`HasCompactPolynomialRankBound ν π hπ` asserts that every such polynomial weight `p` on `K` gives a bounded averaging operator
\[
A_p x=\int_K p(k)\,\pi(k)x\,d\nu(k)
\]
with finite-dimensional range, of complex dimension at most `C * (p.totalDegree + 1)^d` for two natural numbers `C` and `d` independent of `p`. The Bochner integrals and their bounded operator are those of `Langlands.Archimedean.compactAverage`.

`ArchimedeanCompactPolynomialRankStatement` asserts the bound for every irreducible unitary representation of `G` and every Haar measure on `K`, with independent universes for the number field and Hilbert space. The statement covers all natural ranks.

The rank bound is a consequence of Harish-Chandra's compact multiplicity estimate and finite-dimensional polynomial counting. Both the left and the right translates of `p` lie in the restrictions of degree at most `p.totalDegree`, since multiplication by a fixed matrix acts real-linearly on matrix coordinates. On every compact type on which `A_p` acts nontrivially, this space contains the matrix coefficients of the type, by orthogonality. Its dimension therefore controls the sum of squares of the dimensions of the types that contribute. A multiplicity bound by the dimension of the compact type then controls the rank of `A_p`. Equivalently, the polynomial identity argument can be applied to the compact-averaging operator directly.

The source for the multiplicity estimate and the polynomial identity argument is Anthony W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples*, 1986, Chapter VIII §2, Theorem 8.1 and its proof, printed pp. 205–207 (PDF pp. 219–221). Literature ID `knapp-1986-representation-theory-semisimple-groups`, SHA-256 `a8ae5776789005035f477f7ea79ee4a268ad43b2d84a607d55b4bedf763dbe75`. The statement here is a derived polynomial-coordinate formulation for the full archimedean matrix group. The identity-component argument transfers the multiplicity estimate to this group with a possible constant depending on its finite component group. The triangular-times-compact decomposition also permits the polynomial identity argument directly on the full group.
