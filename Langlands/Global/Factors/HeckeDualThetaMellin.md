# The dual Mellin identity of the Fourier theta series of a divisor

Worker 1692 supplies this per-divisor identity, which Worker 1798 requested for the
global assembly of Hecke's functional equation. It is the dual
(Fourier-side) counterpart of the primal Mellin identity of the theta series attached to a
finite divisor class. It is the step of Hecke's theta-series proof (and of the global
unfolding in Tate's thesis) in which the inverted theta series is integrated against the
mixed character over the fundamental cone. The result is the archimedean integral of the
Gaussian test function times the finite divisor Dirichlet series. Everything concerns an
actual Hecke character `χ` of a number field `K` in an unrestricted universe `u`, together
with:

- the supplied finite unitary additive characters `ψf v` and self-dual Haar measures `μ v`;
- a finite set `Sψ` outside which `ψf v` has additive conductor `0`;
- presentations `dR`, `dC` of the infinite components of `χ` and `dR'`, `dC'` of those of
  `χ⁻¹`, given as hypotheses in the target's sense.

Write `χ_∞` and `χ_∞'` for the `Hecke.mixedCharFun` of `(dR, dC)` and `(dR', dC')`. Write
`b_d` for the Fourier theta coefficient `fourierThetaCoeff χ ψf μ d` of package B4 and
`c_s(D)` for the actual Fourier divisor Euler coefficient
`DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) D`. `N` is the
mixed norm, `w = Units.torsionOrder K`, and `C` is the fundamental cone `fundamentalCone K`.

## Statements (namespace `Langlands.Global.HeckeTheta`)

- `fourierThetaCoeff_inv_mul_eq_coefficient`: for every finite divisor `d`, nonzero
  `γ : Kˣ`, complex `s` and finite set `S` outside which the zeroth Fourier shell weight is
  `1`,
  `b_d(γ⁻¹) · χ_∞(γ)⁻¹ · N(γ)^s = c_s(-principalDivisor γ - d) · dualClassFactor χ d s`.
  This is the B4 identity `fourierThetaCoeff_mul_eq_coefficient` applied to `γ⁻¹`. Its
  ingredients are `principalDivisor γ⁻¹ = -principalDivisor γ` and
  `χ_∞(γ⁻¹) = χ_∞(γ)⁻¹`, which follows from the multiplicativity of `mixedCharFun` and
  `N(γ) ≠ 0`. The last ingredient is `N(γ⁻¹)^(-s) = N(γ)^s`, valid because `N(γ) > 0`.
- `dualPrincipalSeries χ ψf μ S d s` is the definition
  `∑'_{p ∈ principalDivisors K} c_s(-p - d)`, the sum of the Fourier divisor Euler
  coefficients over the divisor class of `-d`. It is Lean's unconditional `tsum`, which is
  `0` when the family is not summable.
- `hasSum_dualPrincipalSeries`: if `D ↦ ‖c_s(D)‖` is summable over all finite divisors,
  the family `p ↦ c_s(-p - d)` has sum `dualPrincipalSeries χ ψf μ S d s`. The proof notes
  that `p ↦ -p - d` is injective, so this family is absolutely summable as a subfamily.
- `classFactor_one_sub_mul_integral_fourierTheta` (the dual per-divisor Mellin identity).
  Its hypotheses are:
  - `G` on the mixed space satisfies `‖G z‖ ≤ C exp(-c‖z‖²)` with `c > 0`;
  - `S` contains every finite place where the zeroth Fourier shell weight at `s` is not `1`;
  - the coefficients `c_s(D)` are absolutely summable over all finite divisors `D`;
  - `G χ_∞' N^(s-1)` is integrable.

  Then
  `classFactor χ d (1 - s) · ∫_C (θ(b_d, G)(x⁻¹) - b_d(0) G(0)) χ_∞(x) N(x)^(-s-1) dx
    = w · (∫_V G(y) χ_∞'(y) N(y)^(s-1) dy) · ∑'_{p principal} c_s(-p - d)`,
  where `θ(b, G)(x) = ∑_{γ ∈ K} b(γ) G(γ x)` is `Hecke.thetaSeries` and `p` runs over the
  principal divisors `principalDivisors K` of package B1/B2. The theorem writes this sum
  out exactly in the form Worker 1798 requested. By definition it is
  `dualPrincipalSeries χ ψf μ S d s`.

## Proof

The proof follows the route Worker 1798 suggested.

1. **Archimedean integral.** By `mixedCharFun_dual_eq_inv_apply` (theta bridges),
   `χ_∞'(y) = χ_∞(y⁻¹)` for all `y`. Worker 1798's `Hecke.integral_inv_eq_and_integrable`
   (module `ThetaUnfolding`) says that the inversion `y ↦ y⁻¹` turns
   `∫ G(y⁻¹) χ_∞(y) N(y)^(-s-1)` into `∫ G(y) χ_∞(y⁻¹) N(y)^(s-1)` and preserves
   integrability. The integrability hypothesis therefore gives the integrability the
   unfolding needs, and the two archimedean integrals agree.
2. **Coefficient data.** B4 supplies a divisor `e` such that `b_d` is supported in
   `latticeIdeal e` (`exists_fourierThetaCoeff_support`), a uniform bound on `b_d`
   (`exists_norm_fourierThetaCoeff_le`) and the unit covariance
   `b_d(u γ) = χ_∞(u)⁻¹ b_d(γ)` (`fourierThetaCoeff_unit_mul`).
3. **Unfolding.** Worker 1798's `Hecke.integral_thetaSeries_inv_unfold` is applied with:
   - the mixed character `χ_∞`, which is multiplicative and sends `1` to `1`
     (`Hecke.mixedCharFun_mul`, `Hecke.mixedCharFun_one` of module `MixedCharacter`);
   - the principal generators `principalGenerator` and the equivalence
     `principalUnitsEquiv : principalDivisors K × (𝓞 K)ˣ ≃ Kˣ` of B1/B2, whose
     compatibility holds by definition.

   It writes the cone integral as
   `w ∑'_p b_d(gen p⁻¹) χ_∞(gen p)⁻¹ N(gen p)^s ∫ G(y⁻¹) χ_∞(y) N(y)^(-s-1) dy`.
   The summability hypothesis of the unfolding is checked from the first statement: in
   norms, each term is `‖c_s(-p - d)‖ · ‖dualClassFactor χ d s‖`. Since
   `principalDivisor (gen p) = p` (`principalDivisor_principalGenerator`) and
   `p ↦ -p - d` is injective, this is summable by the assumed absolute summability of
   `c_s`.
4. **Conclusion.** By the first statement, the `p`-th term is
   `c_s(-p - d) · dualClassFactor χ d s`. The constant factor is pulled out of the sum.
   The theta bridge identity
   `classFactor χ d (1 - s) · dualClassFactor χ d s = 1`
   (`classFactor_one_sub_mul_dualClassFactor`) then removes the class factors by a ring
   computation.

The module proves only this per-divisor identity. The Poisson summation, the analytic
continuation and the global functional equation of the Hecke `L`-function stay with the
final assembly.
