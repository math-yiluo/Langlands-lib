# The same finite compact-average family after dual transformation

This derived helper implements the transformed compact-average calculation in
JPSS (1983), Section 6.3, printed p.437, immediately before formula (14).

For an actual group function `W`, `adjacentRankDualMiddleAverage` is the compact
middle average of `g ↦ W(w_n*iota(g))`, with inverse transpose `iota`, divided by
the complex Haar mass of the supplied compact open subgroup `K`. It uses the
same canonical `generalLinearHaar` as the original compact average.

If `K` is stable under inverse transpose, the involution implies
`iota^-1(K)=K`. The published preservation of canonical Haar under inverse
transpose gives an exact change of variable on that restricted measure.
Multiplicativity of inverse transpose then proves
`adjacentRankDualMiddleAverage_eq`: the transformed average is the original
average at external arguments `w_n*iota(g)` and `iota(h)`. This change of
variable is an equality of totalized integrals for an arbitrary group
function; it asserts no convergence for such an arbitrary function.

`adjacentRankCompact_middleAverage_and_dual` starts with the published actual
finite separation of compact averages for an admissible representation and
its specified standard Whittaker coefficient image. It chooses the number
`N` and model family `B` before the input model vector `W`, and chooses the
actual bi-smooth matrix coefficients `f` before both external group variables.
The same choices satisfy

```text
average_K W(g*k*h) = sum_i B_i(g) * f_i(h),
average_K dual(W)(g*k*h) = sum_i dual(B_i)(g) * f_i(iota(h)).
```

The second family consists of the actual vectors `dualModelLinearMap B_i`
in the coefficient image of `dualFunctional` on the inverse-transpose pullback
representation. The second matrix functions are literally
`GodementJacquet.coefficientIota f_i`. No unrelated new finite family or
matrix coefficients are selected for the transformed identity, and no
equivalence between the original representation carrier and its coefficient
image is asserted. The specified functional may be zero and the admissible
representation may be reducible.

The canonical p-adic field and Borel structures, original carrier universe,
every natural rank parameter including `r=0`, and unchanged Haar normalization
are retained. This result only separates the compact averages. It does not
establish the subsequent dual finite zeta-product formula, existence of matrix
rational values, a functional equation or either parent gamma/L target.

The original is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions*
(1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
On printed p.437 the same compact average transforms the finite vectors by
the Weyl/inverse-transpose operation and the matrix coefficients by inverse
transpose. The present proof obtains that identity directly from the proved
original finite-average identity and the normalized Haar substitution.
