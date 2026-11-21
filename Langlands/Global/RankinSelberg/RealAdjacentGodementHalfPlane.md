# The paired real corank-one unfoldings on a right half-plane

This internal result removes the two integrability hypotheses from
`RealJacquet.RealAdjacentGodementUnfoldingStatement` for uniform-model
coefficients. It records the half-plane form of Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §8.3, pp. 58–59, (8.3) and (8.4), whose
justification Jacquet gives by absolute convergence for `Re s ≫ 0`.

`RealJacquet.RealAdjacentGodementHalfPlaneStatement` has the data and
notation of the unfolding statement:

* quotient measure data `D`, a unit `a` and a real character datum `c`;
* a square-matrix Schwartz test `F` and a row Schwartz test `f`;
* `U` in the uniform model with parameter `-a`, whose pointwise dual `Ũ`
  lies in the uniform model with parameter `a`;
* `V` in the uniform model with parameter `a`.

It asserts a real `σ` such that for every `s` with `Re s > σ` both
conclusions of the unfolding statement hold. These are, first, the
ordinary corank-one integral of the separated Godement coefficient `W` and
`V` as the Weyl scalar times the matrix integral of smaller equal-rank
integrals. Second, the actual dual block integral as `c((-1)^(r+1))` times
that scalar times the analogous integral for the duals.

## Proof

The Library's `realUniformWhittakerRegularity` gives three facts for each
model element: the left unipotent law, smoothness, and polynomial
height growth with one common exponent for all right derivatives.
`RealWhittakerGauge.exists_gauge_bound` turns these into the gauge
estimate. Since the characters for `-a` and `a` multiply to one, `U(u g) V(u g z)`
equals `U(g) V(g z)` for upper unipotent `u`.

For the dual side, `Ṽ(x z)` is the dual of `y ↦ V(y ι(z))`. Here `ι` is
inverse transpose, which is multiplicative. So the published
`dual_mul_invariant` transfers the invariance to `Ũ` and `Ṽ`. The theorem
`realMatrixHeight_inverseTranspose` shows that inverse transpose preserves
the real matrix height: the matrix and inverse entries are exchanged and
transposed. Together with submultiplicativity of the height, this bounds
`‖Ṽ g‖` by a constant times the height of the long Weyl element to a power,
times the height of `g` to the same power. The rectangular and row Fourier
transforms in the two kernels are Schwartz functions, hence continuous and
rapidly decreasing.

`realAdjacentConvergence` therefore gives a half-plane for each kernel.
On the larger of the two, `realAdjacentGodementUnfolding` applies.

Only corank one and separated tests are treated. No spanning of the
uniform model, meromorphic continuation or functional equation is claimed.
