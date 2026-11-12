# The forward integral of a dual-translated zero-cell vector

Module `Langlands.Representation.RankinSelberg.HighlyRamified.EssentialDualIntegral`.

This module is an internal step of the proof of the level of zero-cell Kirillov lifts for
generic representations with `L(s, π) = 1`. It follows the idea of Jacquet,
Piatetski-Shapiro and Shalika (Conducteur des représentations du groupe linéaire, Math.
Ann. 256 (1981), proof of Theorem (5.1)(ii), printed p. 211): compare a vector with the
dual of a translated essential vector through the functional equation against unramified
principal series. The statements below are formulated for this proof; they are not
quoted from the literature.

Throughout, `F` is a p-adic field with its canonical topology, valuation and Borel
structures, `q` its residue cardinality, `ϖ` its canonical uniformizer unit and `|·|`
the normalized absolute value.

## Auxiliary statements

- `ofReal_zpow_cpow_eq hq N s`: for a positive integer `q`, the complex power
  `(q^N)^(s - 1/2)` of the real number `q^N` equals `q^(-N/2) · (q^(-s))^(-N)`, where
  `q^(-s)` is the Library's `spectralPoint q s`.
- `inverseTranspose_mem_integralSubgroup`, `weylLong_mem_integralSubgroup`,
  `neg_one_mem_integralSubgroup`: the inverse transpose of an element of `GL_(r+1)(O)`,
  the long Weyl element and `-1` all lie in `GL_(r+1)(O)`
  (`Conductor.integralSubgroup` of the valuation integers).
- `abv_det_scalar_inv n m`: the normalized absolute value of the determinant of
  `(ϖ^m I_(n+2))⁻¹` is `q^((n+2) m)`.

## Main statement

`forward_corankOne_dualTranslate_eq F ψ hψ ν π ℓ hℓ c m v' hv' z hz hG`. Let `ψ` be an
additive character of conductor exponent zero (`Conductor.HasIntegerConductor ψ`), `ν` a
Haar measure, `π` a representation of `GL_(n+3)(F)` on a complex vector space and `ℓ` a
nonzero `ψ`-Whittaker functional. Let `v'` be a vector whose Whittaker function for the
inverse-transpose pullback `π^ι` and the first dual functional of `ℓ` agrees, on the
mirabolic subgroup (last row `(0, …, 0, 1)`), with the zero-cell function
`zeroCellWhittaker` for `ψ̄ = ψ.scale (-1)` and `ϖ`. Let `Y` be the `ℓ`-Whittaker function
of `π^ι(d) v'` with `d = diag(ϖ^m I_(n+2), 1)` (`rankInclusion 1` of the scalar matrix).
Let `z ∈ (ℂˣ)^(n+2)` have all entries of norm one, and assume that
`IsPadicSymmetricGammaFactor F ψ ν π I(z) G` holds for the unramified principal series
`I(z) = Unramified.principalSeriesOfTuple F z` and the monomial

`G = rationalEpsilonMonomial (c^(n+2) (∏ z_i)^m) ((n+2) m)`.

Then there is `a ∈ ℝ` such that for every `s` with `Re s > a` the corank-one integral of
`Y` against Jacquet's spherical function `W(·; z; ψ̄)`
(`Conductor.inverseSphericalWhittaker`) for the quotient measure
`unipotentQuotientHaar F (n + 1)` converges and equals

`q^(-N/2) · q^N / c^(n+2)`, with `N = (n+2) m`.

The constant does not depend on `z`.

## Proof

1. The symmetric gamma relation gives the pair relation for `(π, I(z))`
   (`isPadicSymmetricGammaFactor_of_le`), and unfolding it (`isPairGammaFactor_of_lt`)
   gives a nonzero inverse Whittaker functional `ℓσ` of `I(z)`. By the module
   `UnitarySpherical`, `I(z)` has a normalized spherical test vector for `ℓσ` whose
   Whittaker function `f'` is `W(·; z; ψ̄)`. It is right `GL_(n+2)(O)`-invariant with
   `f'(1) = 1`.
2. The central character of `I(z)` is `∏ χ_i` (`principalSeriesOfTuple_hasGLCentralCharacter`),
   whose value at `ϖ^m` is `K = (∏ z_i)^m`. So `f'(h ϖ^m) = K f'(h)` (Library
   `model_mul_scalar`).
3. The second dual function `X(g) = f'(w₀ ᵗg⁻¹)` of `f'` is right `GL_(n+2)(O)`-invariant,
   satisfies `X(1) = 1`, and satisfies `X(g a⁻¹) = K X(g)` for `a = ϖ^m I_(n+2)`, because
   `ᵗa = a`.
4. The first dual function of `Y` is the right translate by `d` of the Whittaker function
   of `v'` (`firstDualFunction_coefficient`). The module `ZeroCellDualIntegral` therefore
   evaluates the dual corank-one integral for every `s` as
   `K · |det a⁻¹|^(s - 1/2) = K q^(-N/2) (q^(-s))^(-N)`, using `abv_det_scalar_inv` and
   `ofReal_zpow_cpow_eq`.
5. The Library theorem `corankOne_eq_const_of_gamma_monomial` (module `ForwardConstant`)
   combines the functional equation with this monomial dual integral and the monomial
   gamma factor. It gives a scalar `ζ` by which `-1` acts on the Whittaker model of
   `I(z)`, and on a right half-plane the forward integral equals
   `ζ^(-(n+2)) C⁻¹ K q^(-N/2) q^N` with `C = c^(n+2) K`.
6. Since `-1 ∈ GL_(n+2)(O)` and `f'` is right `GL_(n+2)(O)`-invariant with `f'(1) = 1`,
   `ζ = 1`. The factor `K` cancels, which gives the stated constant.
7. The constant is nonzero. A non-integrable integrand would make the Bochner integral
   `0` (`integral_undef`), so the integrand converges on the same half-plane.

The main theorem needs `set_option maxHeartbeats 1000000`. With the default limit,
elaborating the declaration times out.

## Use

The next step compares, for every norm-one `z`, this constant with the integral of a
zero-cell lift `w` of `π` against the same spherical function (also constant, by the
module `ZeroCellDualIntegral`). The module `UnitarySeparation` then shows that `w` is a
multiple of `Y` on the mirabolic subgroup.
