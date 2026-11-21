# Prime and central residue-cardinality normalization of the same rank height

Suppose the original order-linear local rigidifier is measured with prime
`p`, and its central coefficient ring has uniformizer `ϖ` and residue
cardinality `p^l`. Assume `p = u ϖ^e` for a unit `u`. The central source has
its actual `ϖ`-height, and the central target is `ϖ`-divisible.

`HeightPresentation.centralNumerator_hasHeight` carries the actual finite
kernel model of a prime-normalized numerator to its centrally linear
counterpart. On a presenting open with a point, the coefficient ring is
nontrivial. The rank of the central numerator on that open is constant.
Computing it at one residue field gives its exponent in the central residue
cardinality. `HeightPresentation.centralWithHeight` replaces the denominator
`p^n` by `ϖ^(en)` and corrects the numerator by the inverse of `u^n`. The unit
correction preserves the actual numerator rank. The prime-power and
uniformizer-power denominator kernels also have the same represented rank.

`HeightPresentation.exists_centralHeightPresentation` consequently relates
the two signed rank differences by the exact factor `l`. For positive `l`,
`HasHeightFunction.centralScalarSection_divide` applies this relation on the
presenting opens of the actual central section. It verifies the height
function obtained by dividing every prime-normalized value by `l` and proves
that those divisions are exact.

This is the scalar normalization in the primal part of the split comparison
of Rapoport–Zink, (6.17) and Lemma 6.44, printed pp. 309–310. Harris 1997,
Appendix, printed pp. 112–113, uses prime-normalized kernel ranks and denotes
the residue degree by `f`. The further division-degree normalization belongs
to the component map.
