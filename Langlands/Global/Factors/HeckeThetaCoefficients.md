# Finite theta coefficients of actual Hecke characters

Worker 1692 builds these internal coefficient identities for the global Hecke
unfolding requested by Worker 1798 (package B3). Everything is stated for an
actual Hecke character `χ : HeckeCharacter K` of a number field `K` in
unrestricted universe `u`, its actual finite components
`χ.finiteComponent v`, the Library's actual local Euler tests `eulerTest`, the
actual uniformizers `uniformizerUnit` and the finite divisors
`FinitePlaceDivisor K`. No archimedean data is assumed except where a theorem
explicitly takes the real and complex presentations `dR`, `hR`, `dC`, `hC` of
the actual infinite components; then `χV` below means
`Hecke.mixedCharFun` built from their parities, exponents and weights, as in
`HeckeFunctionalEquation.character_eq_mixed_mul_finite`.

## Local lemmas (namespace `Langlands.LocalFactor.PadicAbelian`)

- `ord_uniformizerUnit_zpow`: the order of `π ^ k` is `k`; and
  `ord_uniformizerUnit_zpow_inv_mul`: `(π ^ ord x)⁻¹ * x` has order zero.
- `character_eq_one_of_conductor_eq_zero`: a quasicharacter of multiplicative
  conductor zero is one on units of order zero (the Library conductor
  characterization at level zero).
- `shellMellinTerm_eq_of_covariant`: if `f (x * w) = η(w)⁻¹ f(x)` for all order-zero
  units `w`, then the shell Mellin term of order `k` equals
  `f(π^k w) η(π^k w) q^(-s k)` (written with `spectralVariable`) for every
  order-zero unit `w`. `shellMellinTerm_ord_of_covariant` specializes it to
  `w = (π ^ ord x)⁻¹ x`, evaluating the term of order `ord x` at `x` itself, and
  `shellMellinTerm_eulerTest_ord` applies it to the actual Euler test using the
  Library covariance `eulerTest_mul_integralUnit`.
- `norm_eulerTest_le_one`, `mem_additiveLattice_zero_of_eulerTest_ne_zero` and
  `eulerTest_eq_one_of_mem`: the actual Euler test has norm at most one, vanishes
  off the integer ring, and is one on the integer ring when the conductor is
  zero. These unfold the Library formula `eulerTest_coe` (indicator of the
  integers when unramified, inverse character extension on integral units
  otherwise).

## Global elements at finite places (namespace `Langlands.Global.HeckeTheta`)

`localUnit v a` is the image of `a : Kˣ` as a unit of the finite completion at
`v`; `ord_localUnit` identifies its order with the coefficient of
`principalDivisor a` at `v`. `exists_finset_conductor_eq_zero` gives a finite set
outside which every finite component has conductor zero (from the existing
unramified-places theorem). Hence `exists_finset_finiteComponent_localUnit_eq_one`
gives a finite set containing the support of `principalDivisor a` outside which
`χ_v(a) = 1`.

`finprod_finiteComponent_localUnit` is the finite half of the product formula:
`∏ᶠ v, χ_v(a) = (χV(ι a))⁻¹`, where `ι = mixedEmbedding K`. It applies
`character_eq_mixed_mul_finite` to the diagonal idele of `a`, on which the actual
Hecke character is one, together with the existing identification of its
mixed infinite coordinate with `ι a`.

`mixedNorm_cpow_eq_prod`: for every finite set `S` containing the support of
`principalDivisor a`, `N(ι a) ^ (-s)` equals `∏ v ∈ S, spectralVariable_v(s) ^
(principalDivisor a v)`. The mixed norm is `|N_{K/ℚ}(a)|`, the existing theorem
`HeckeDivisor.norm_principalDivisor` writes it as the product of the prime norms
to the divisor coefficients, and the complex power of this positive real
product is the product of the exponentials of the logarithms, which match the
local spectral variables through the existing residue-cardinality comparison.

## Theta coefficients

For `d : FinitePlaceDivisor K` and `γ : K`,

- `thetaFactor χ d γ v := eulerTest_v(γ π_v ^ d(v))`;
- `thetaCoeff χ d γ := ∏ᶠ v, thetaFactor χ d γ v`;
- `classFactor χ d s := ∏ v ∈ d.support, (χ_v(π_v) · spectralVariable_v(s)) ^ d(v)`.

`exists_finset_thetaFactor_eq_one` shows the factors are one outside the union
of the ramified places, the support of `d` and the finitely many places where
`γ` is not integral (`Hecke.finite_setOf_not_mem_additiveLattice_zero`); so
`mulSupport_thetaFactor_finite` holds and `thetaCoeff_eq_prod` evaluates the
unordered product as the finite product over any set outside which the factors
are one.

The four requested properties are proved:

1. `mem_latticeIdeal_of_thetaCoeff_ne_zero`: a nonzero coefficient forces
   `γ ∈ Hecke.latticeIdeal d`. Each local factor is nonzero, so
   `γ π_v ^ d(v)` is integral and `γ` lies in the local lattice of level `d(v)`;
   `Hecke.mem_latticeIdeal_iff_forall_mem` concludes.
2. `norm_thetaCoeff_le_one`: `‖thetaCoeff χ d γ‖ ≤ 1`, a finite product of local
   bounds.
3. `thetaFactor_unit_mul` (each factor is multiplied by `χ_v(u)⁻¹`, since a
   global integral unit has local order zero by
   `principalDivisor_units_map`) and `thetaCoeff_unit_mul`: for
   `u : (𝓞 K)ˣ`, `thetaCoeff χ d (u γ) = χV(ι u) · thetaCoeff χ d γ`, using the
   product formula above for `u`.
4. `thetaCoeff_mul_eq_coefficient`: for `γ : Kˣ` and every `s`,
   `thetaCoeff χ d γ · (χV(ι γ))⁻¹ · N(ι γ) ^ (-s) · classFactor χ d s` equals
   `DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s)
   (principalDivisor γ + d)`. On a common finite set the left side becomes a
   product of local terms `eulerTest_v(x_v) χ_v(x_v) spectralVariable_v(s) ^
   ord(x_v)` with `x_v = γ π_v ^ d(v)`, whose order is
   `principalDivisor γ v + d(v)`; `shellMellinTerm_eulerTest_ord` identifies
   each with the actual shell weight at that order, and the zeroth shell
   weight is one (`shellWeight_zero`).

These results do not establish the Fourier-side coefficients, Poisson
summation, unit-cone integrals, analytic continuation or the global functional
equation.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
