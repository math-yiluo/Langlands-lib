# Proof of Schwartz assembly in root coordinates

`Langlands.RankinSelberg.rootSchwartzAssembly` proves
`RootSchwartzAssemblyStatement F n` for every Hausdorff field with continuous
ring operations, with the statement's full universe and rank parameters.

The proof first obtains a nonzero entry in the last row of `k`. Otherwise the
row would vanish and the determinant would be zero, contradicting
invertibility. It then uses the formula in the statement as the underlying
function `f`.

Coordinate restriction and multiplication of the last coordinate by the
fixed last row are continuous. Composing the three locally constant input
tests with these maps and multiplying proves local constancy of `f`.

For compact support, choose the nonzero row entry `v_j`. The map
`(y,z) ↦ Fin.snoc y (z_j / v_j)` is continuous, so the image of
`tsupport φ × tsupport Φ` is compact. If `f x` is nonzero, its first and third
factors are nonzero. Thus the prefix of `x` and `x_n • lastRow k` lie in the
respective topological supports. Applying the displayed map to that pair
recovers `x`: division by `v_j` cancels the nonzero row entry and `Fin.snoc`
reattaches the final coordinate. This contains the ordinary support of `f`
in a compact set; the Hausdorff property then gives compact topological
support. The second root test requires no additional support bound.

Finally the proof packages `f` with these two properties as a Schwartz–Bruhat
function. Its pointwise identity is definitional. The argument works also
for `n = 0` and for zero input tests. This internal elementary proof has no
analytic or representation-theoretic assumptions and proves only the stated
Schwartz assembly result.
