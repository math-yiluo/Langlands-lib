# A uniform height bound on actual binary special-linear rational orbits

This derived module constructs a uniform height bound for the standard representation
of the actual group scheme `SL₂` over any number field `F : Type u`. It uses the
published adelic `GL₂` Hermite theorem in `PrimitiveAdelicGL2` and the actual
special-linear point equivalence. It assumes no compact quotient, fundamental set,
height bound or chamber-reduction theorem.

`standardRepresentation` is the actual inclusion of the determinant-one group scheme
into `GL₂`. Its affine matrix is the usual inclusion of the determinant-one matrix
classified by the point, on every affine test algebra. The adelic specialization is
therefore the same matrix, and `det_adelicMatrix` proves its determinant is the identity
idele.

`exists_specialLinear_firstColumn` proves that every nonzero vector in `F²` is the
first column of a rational determinant-one matrix. If its first coordinate is
nonzero, the second column is `(0, v₀⁻¹)`; otherwise its second coordinate is nonzero
and the second column is `(-v₁⁻¹, 0)`. The determinants and first columns are checked
directly.

`HasUniformRationalOrbitHeightBound` says that one real constant `C > 0` works for
every actual adelic point `g`: some actual rational `SL₂` point `q` has selected-vector
height at most `C` at `g q`, for the first coordinate vector `e₀`. The height is the
published normalized primitive-vector height pulled back through the actual algebraic
representation, not a matrix-and-inverse height.

`hasUniformRationalOrbitHeightBound` proves this assertion. The `GL₂` Hermite theorem
supplies a nonzero rational vector of height at most `C` times the square root of the
normalized determinant norm. The determinant identity makes the latter factor one.
The determinant-one column completion and the affine point equivalence construct an
actual rational `SL₂` point carrying `e₀` to that vector. Naturality of the actual
representation and the rational-translation identity for `orbitHeight` give the
required inequality with the same constant.

`exists_uniform_bound_on_approximate_minima` then bounds every approximate minimum
by `c C`, uniformly in the adelic point. Its premise is the explicit inequality
`H(g) ≤ c H(g q)` for every actual rational `SL₂` point, with `c ≥ 0`. Apply this
inequality to the constructed small translate and multiply its bound by `c`.

The result is specialized to the actual split binary special-linear group and its
standard representation. It constructs the uniform bound in this case. It does not
identify a general rank-one group with `SL₂`, treat an arbitrary parabolic eigenline,
construct the Siegel factors or prove the host chamber-reduction statement.
