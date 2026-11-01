# The actual quotient shear and fixed-shell Fubini identity

This derived helper supplies the change of variables between formulas
(4) and (5) in JPSS (1983), Section 6.3, printed page 433.

For any topological group and any subgroup, the actual left-coset
quotient admits the homeomorphism `(H g,h) -> (H (g h),h)`, with
inverse `(H g,h) -> (H (g h^-1),h)`. No normality hypothesis is used.
Joint continuity of right translation descends through the product
of the open quotient map with the identity. The inverse identities
follow from the group laws on representatives.

For supplied s-finite Borel measures on the quotient and the group,
with second-countable topologies, right invariance of the quotient
measure implies that this shear preserves their product measure.
The proof swaps the two coordinates, applies the measure-preserving
skew-product theorem to right translation in the quotient coordinate,
then swaps back. The inverse shear also preserves the measure.
Integrability is therefore equivalent before and after inverse shear,
and their integrals agree exactly, without a normalizing scalar.

The adjacent-rank specialization retains every canonical p-adic field,
every supplied compatible quotient measure, and the actual
`generalLinearHaar`. Countability, local compactness and regularity
give all the required measure instances. Its after-shear kernel is
the fixed-total-shell kernel of `AdjacentRankJointShell`. Its
before-shear kernel is its actual composition with the inverse
homeomorphism. On representatives it is exactly

`1_(ord(det g)=m) W(g h^-1) W'(g)
 phi(lastRow(g h^-1)) Phi(h) a(h)`.

Here `W` is an actual coefficient-image vector of an arbitrary smooth
representation in independent universe `uV`; `W'` is an
inverse-character Whittaker function with continuous values. The
row and square matrix tests are genuine Schwartz–Bruhat tests,
and `a` is any continuous scalar multiplier. In source column notation,
the row argument equals `h^iota (transpose g) epsilon`, because
`iota` is inverse transpose.

The compact joint support already proved for the after-shear kernel
gives its absolute integrability. Measure preservation transfers
this to the before-shear kernel. Fubini then gives integrability of
the asserted iterated integrals, equality of the before and after
iterated quotient-then-group integrals, and equality with the reversed
group-then-quotient integral. The equalities are accompanied by genuine
joint integrability, rather than using totalized integrals without
convergence.

The original source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 486 visually reread printed page 433 while implementing this
helper, after reading the surrounding printed pages 432–436.
The generic quotient homeomorphism and measure argument are internal
formal packaging of its change of variables. This helper does not
identify the initial scalar model coefficient with formula (4), and
does not prove Laurent convolution, global series convergence,
functional equations, or either parent gamma/L statement.
