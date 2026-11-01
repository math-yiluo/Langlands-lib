# The adjacent-rank model-star identity at the base ambient point

The theorem `adjacentRankModelStar_base` proves
`AdjacentRankBaseModelStarIdentity F psi nu hself sigma ell chi` for every
smooth complex representation `sigma` on an arbitrary complex module. The
field and module universes are independent. The field has its canonical
p-adic topology, all natural `r`, including zero, are allowed, and the Haar
measures are exactly `generalLinearHaar F.Carrier r` and
`unipotentHaar F.Carrier r`. No irreducibility, nonzero functional, topology
on the representation module, or extra convergence hypothesis is needed.

The base ambient point is `a0 = w_(r+2) * zeta`. For every original algebraic
test tensor `Psi`, the conclusion identifies the existing model integral
at `a0` with the integral of `adjacentRankTransformedIntegrand` applied to
the full plus Fourier transform of the Schwartz factor and ambient point
one. The original additive character, coefficient image, and fixed
`rho0_psi` action are retained throughout. The transformed coefficient
argument is `w_(r+1) * inverseTranspose(h^-1)`, the quasicharacter is
`chi^-1`, and the inner determinant exponent is `r/2`, as in the target.

For a pure tensor `Phi tensor W`, the proof specializes the published
scalar `adjacentRankUnipotentFourier` theorem to
`phi_h = RowTranslate h (T.symm Phi)`, where `T` is the inverse-character
partial Fourier transform. The two Fourier orbit adapters express its
source evaluation as `rho0_psi(a0) Phi` at `K(h*u)` and its target
evaluation as the full plus Fourier transform of `Phi` at
`K((inverseTranspose(h)*w)*u)`, with determinant factors `|det h|` and
`|det h|^(-(r+1))`, respectively.

The coefficient orbit formulas give the inverse standard unipotent
character on the source side and the standard character on the target
side, both multiplying the same `W(h^-1)`. The source character weight is
`chi(det h)`, whereas the reflected target contributes
`chi^-1(det w) * chi(det h)`. Since
`r/2 + 1 - (r+1) = -r/2`, the determinant factors balance. Multiplying
the scalar Fourier equality by the factors constant on each orbit
therefore gives
`integral_N source(h*u) = chi(det w) *
integral_N target((inverseTranspose(h)*w)*u)`.
This is `adjacentRankModelStar_pure_right_averages`.

The source and target scalar functions are continuous with compact
support by the imported whole-tensor regularity theorems. The reflected
right-average integration adapter thus gives the corresponding integrals
over GL with precisely the existing Haar normalizations. The theorem
`adjacentRankModelStarBase_of_pure_integrals` extends this comparison from
pure tensors to every algebraic tensor. At each addition step it uses
continuity and compact support to establish actual integrability before
applying integral additivity.

Finally, expansion of the unsigned Weyl determinant along its first row
gives `det(w_(n+1)) = (-1)^n * det(w_n)`. Together with the existing
determinant of `zeta`, this gives `det(a0) = det(w_(r+1))`. The absolute
determinant of `a0` is one, and its model prefactor cancels the remaining
`chi(det w)` because `w*w = 1`. This proves the stated base identity.

This is an internal assembly of the scalar Fourier theorem, exact
Fourier and coefficient orbit formulas, compact-support results, and
normalized Haar integration adapters. The elementary first-row Weyl
determinant argument reuses the published
`RankOneGammaTwist.determinant_weylLong_succ` from
`RankOneGammaTwistAlgebra`.
The general ambient-point reduction and the two convergence conclusions
of the closed `AdjacentRankModelStarStatement` are supplied separately;
this module proves the base equality used by that final assembly.
