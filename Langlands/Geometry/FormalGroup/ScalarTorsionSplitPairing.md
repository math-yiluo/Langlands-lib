# The split evaluation pairing on scalar-power torsion

For a commutative group scheme `G`, a `Cartier.PointCharacterPair G T`
consists of a point of `G` over the test scheme `T` and a relative
Cartier character. The character group is written multiplicatively.

`Cartier.splitPairing` takes pairs `(x, χ)` and `(y, ψ)` to
`ψ(x) / χ(y)` in the multiplicative group over the test scheme.
It is multiplicative in each pair, has value one on the diagonal,
and inverts on interchange of the pairs. It commutes with restriction
along maps of test schemes by naturality of Cartier evaluation.

For two endomorphisms `f` and `g` of `G`,
`Cartier.splitMap` acts by `f` on the point and by precomposition
with `g` on the character. The adjoint equation is the corresponding
operation with `g` and `f` interchanged. Both evaluations in the
equation reduce by the Library's Cartier precomposition formula.

`IsPiDivisible.splitTorsionPairing` specializes the formula to the actual
group scheme of the kernel of `[π^n]` of a scalar-divisible coordinated
formal module. This gives the point-pairing calculation behind the
tautological polarization of `X × X̂` in Harris 1997, Appendix, printed pp. 112–113
(PDF pages 38–39), with the sign chosen by evaluating the second
character on the first point in the numerator. The adjoint equation
is the split-order interchange at the level of kernel endomorphisms.
Existence of finite flat Cartier dual models, perfectness and
compatibility of polarizations across torsion levels require further results.
