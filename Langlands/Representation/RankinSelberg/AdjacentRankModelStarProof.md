# Fixed-character adjacent-rank model-star identity

`Langlands.RankinSelberg.adjacentRankModelStar.{uF,uV}` proves exactly the
published closed proposition `AdjacentRankModelStarStatement.{uF,uV}`.
All analytic structures are those of the canonical p-adic field. The
nontrivial continuous unitary character psi, additive Haar nu and certificate
`IsSelfDual psi nu` remain supplied. The original complex module V has its
independent universe and carries no topology or norm. The full standard
Whittaker-type hypothesis is retained, with every functional ell, including
zero, every continuous quasicharacter chi, every whole algebraic test tensor
Psi, every ambient g and every natural r, including zero.

Put n=r+1, t=r+2, iota(h)=(h^-1)^transpose, w the unsigned long Weyl matrix,
zeta=diag(-1,...,-1,1), and K(h)=[h,iota(h) epsilon]. Write H for the full
plus-psi Fourier transform of the Schwartz factor and T for the minus-sign
last-column Fourier equivalence. The action remains rho0_psi=T R T^-1 on
both sides. H is tensored with the identity on the actual original coefficient
image. In particular, the right coefficient is evaluated literally at
`w_n*iota(h^-1)`; it is not replaced by an identification of coefficient
spaces for different characters. Every determinant weight uses the canonical
residue-normalized absolute value and the existing complex-power convention.
Both outer integrals use exactly `generalLinearHaar F.Carrier r`.

The final assembly has three parts. `adjacentRankModelConvergence` proves
actual convergence of the source model at `w_t*iota(g)`.
`adjacentRankTransformed_integrable_of_isSmooth` proves integrability of the
literal right integrand after applying H and rho0_psi(zeta*g). Smoothness
comes from the admissibility component of the full Whittaker-type premise.
For a pure tensor, compact support of the transformed coefficient product
follows by expressing that coefficient as an actual coefficient of the
inverse-transpose pullback representation and applying the published
simple-root support bound. This use of an inverse-character coefficient to
prove support does not change the Fourier action. Continuity, the locally
finite inner Haar, and finite tensor sums then give integrability.

The equality follows from `adjacentRankModelStar_base` and
`adjacentRankModelStar_equality_of_base`. The base theorem establishes the
identity at `w_t*zeta`. Its scalar input is the published closed theorem
`Langlands.HarmonicAnalysis.adjacentRankUnipotentFourier`, applied to
`L_h(T^-1 Phi)`, where `L_h phi(m)=phi(h*m)`. The two formulas in
`AdjacentRankModelStarFourierOrbit` convert the scalar Fourier evaluations
into the source right-unipotent orbit and the reflected right-unipotent orbit
of the full transform, with factors `|det h|` and `|det h|^-n`.
Whittaker covariance, determinant multiplicativity and the normalized weight
identities incorporate the original coefficient and quasicharacter. The
continuous compactly supported functions supplied by
`AdjacentRankModelStarRegularity` can therefore be integrated using
`adjacentRank_integral_eq_of_reflected_right_averages`. That theorem uses the
actual quotient Weil formula and the Haar-preserving substitutions
`h -> iota(h)*w_n` and `u -> w_n*iota(u)*w_n`. Thus its unipotent and general
linear measures are the prescribed shared measures, with no assumed
comparison scalar. Additivity and actual integrability extend the pure
identity to the entire tensor product. The base determinant prefactor
cancels the remaining Weyl quasicharacter constant.

For the passage to arbitrary g, put k=zeta*g. The factorization
`(w_t*zeta)*iota(k)=w_t*iota(g)` moves rho0_psi(iota(k)) into the input test.
The established fixed-character covariance is

```text
H(rho0_psi(iota(k)) Psi) = |det k|^n rho0_psi(k)(H Psi).
```

The source action prefactor is
`chi^-1(det k)*|det k|^(-n/2)`. Multiplying by the Fourier scalar gives
exactly `chi^-1(det k)*|det k|^(n/2)`, with the literal right integrand of
the statement. No convergence or identity premise is added to the closed
theorem.

This implements the fixed-character scalar-integral formulation derived in
`AdjacentRankModelStarStatement.md` from Jacquet, Piatetski-Shapiro and
Shalika, *Rankin-Selberg Convolutions* (1983), Section 6.2 Proposition (1),
printed p.431. The action, partial transform, full plus transform and model
are those of Section 6.1, printed pp.427-429; scalar Lemma (2) and its Fourier
inversion argument are on printed pp.431-432. The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The proof uses only the imported scalar Fourier, Haar, support and covariance
results. It uses no adjacent-rank gamma/L basis, factor existence,
large-positive-twist restriction or later multiplicativity theorem.
