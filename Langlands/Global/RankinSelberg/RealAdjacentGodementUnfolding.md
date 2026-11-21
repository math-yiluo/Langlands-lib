# Paired corank-one unfoldings of a separated real Godement coefficient

This internal comparison combines the published-candidate pieces of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.3, pp. 58–59,
(8.3) and (8.4), for one separated test. Write `m = r+1`,
`H = GL_m(ℝ)`, `η` for the determinant character of `c` and `ηᵛ` for that
of `c.inverse`.

`RealJacquet.RealAdjacentGodementUnfoldingStatement r` concerns the
actual upper function
`W = realAdjacentGodementCoefficient D a (realColumnProduct F f) U c`,
where `F` is a square-matrix Schwartz test, `f` a row Schwartz test, `U`
lies in the uniform model with parameter `-a` and its pointwise dual
`Ũ` lies in the uniform model with parameter `a`. The lower function `V`
lies in the uniform model with parameter `a`. Put
`f̂ = realRowSchwartzFourier m a f`, `F̂ = realRectangularSchwartzFourier a F`
and `b = realAdjacentWeylSign r c`. If the two unfolded joint kernels
are absolutely integrable on the supplied product of quotient and group
measures, the statement asserts:

* the ordinary unequal integral `realUnequalIntegral` of `W` and `V` at `s`
  equals `b` times the integral over `z ∈ H` of the smaller equal-rank
  integral of `U` and `V(· z)` with row test `f̂`, weighted by
  `F(z) η(det z) |det z|^(s + r/2)`;
* the actual dual block integral `realUnequalDualIntegral` with parameter
  `-a` equals `c((-1)^m) b` times the same expression for `Ũ`, `Ṽ`, the
  original row test `f`, the matrix test `F̂` and the character `ηᵛ`.

## Proof

Both model premises give left unipotent laws, with opposite characters
for `U` and `V`. Their product is therefore invariant under the left
unipotent subgroup; the same holds for the duals because the reflected
character of `V` is the character with parameter `-a`. The restriction
identity `realAdjacentGodementRestriction` applies to the separated test
and gives the restricted recursion with scalar `b` and row test `f̂`.
The quotient shear `realLocalAdjacentUnfolding` then proves the first
equation.

For the second, `realUnequalDualIntegral_adjacent` writes the dual block
integral as the ordinary integral of the duals. The reflection
`realGodementColumnReflection`, evaluated at `w_(m+1) g`, identifies the
dual of `W` with `c((-1)^m)` times the Godement coefficient for `-a`,
`Ũ`, `c.inverse` and the rectangular transform of the test. By
`realColumnProduct_fourier` that transform is the separated test
`[A | x] ↦ F̂(A) f̂(x)`. The restriction identity for parameter `-a` yields
the row test `realFourierTransform (-a) f̂`, which equals `f` by
`realRowSchwartzFourier_neg_comp`. The Weyl scalar does not change
under `c.inverse`, since the determinant of a long Weyl element is its own
inverse. The quotient shear completes the proof.

The two integrability hypotheses are retained explicitly; no convergence,
meromorphic continuation or functional equation is claimed, and the
separated tests are not shown to span the needed coefficients.
