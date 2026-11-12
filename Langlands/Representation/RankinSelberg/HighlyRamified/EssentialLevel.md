# The level of the zero-cell Kirillov lift

Module `Langlands.Representation.RankinSelberg.HighlyRamified.EssentialLevel`.

This module is an internal step of the proof of highly ramified gamma stability. It proves
that a zero-cell Kirillov lift of a generic representation `π` of `GL_(n+3)(F)` is fixed by
the level subgroup `K_1(m)` whenever the gamma factors of `π` against all norm-one
unramified principal series are the expected monomials. This is the p-adic case with
`L(s, π) = 1` of the essential-vector part of Jacquet, Piatetski-Shapiro and Shalika
(Conducteur des représentations du groupe linéaire, Math. Ann. 256 (1981), Theorem
(5.1)(ii), printed p. 211). JPSS compare a vector with the dual of a translated essential
vector through the functional equation against unramified representations. The statements
below are formulated for this proof; they are not quoted from the literature.

Throughout, `F` is a p-adic field with its canonical topology, valuation and Borel
structures, `q` its residue cardinality, `ϖ` its canonical uniformizer unit and `|·|`
the normalized absolute value.

## Auxiliary statements

- `abv_uniformizerUnit F`: `|ϖ| = q⁻¹`.
- `coefficient_dualTranslate_apply ψ π ℓ v' d x`: the `ℓ`-Whittaker function of
  `π^ι(d) v'` at `x` equals `W'(w₀ ᵗx⁻¹ d)`, where `π^ι` is the inverse-transpose pullback
  of `π` and `W'` is the Whittaker function of `v'` for `π^ι` and the first dual functional
  of `ℓ`.
- `dualTranslate_restriction_invariant F ψ hψ π ℓ hinj'' u v' hv' g k`: suppose the
  Whittaker function of `v'` for `π^ι` agrees with the zero-cell function for
  `ψ̄ = ψ.scale (-1)` on the mirabolic subgroup, and `π^ι` with its first dual functional
  satisfies mirabolic restriction injectivity. Then the `ℓ`-Whittaker function of
  `π^ι(d) v'`, with `d = diag(u I_(n+2), 1)`, takes the same value at `diag(g k, 1)` and
  `diag(g, 1)` for every `g ∈ GL_(n+2)(F)` and `k ∈ GL_(n+2)(O)`.

## Main statement

`exists_levelFixed_zeroCellLift_of_unit_gamma F ψ hψ ν π hπ c m hG`. Let `ψ` be an
additive character of conductor exponent zero, `ν` a Haar measure, and `π` a
`ψ`-generic representation of `GL_(n+3)(F)` on a complex vector space. Let `c ∈ ℂˣ` and
`m ∈ ℕ`. Assume that for every `z ∈ (ℂˣ)^(n+2)` with all entries of norm one,

`IsPadicSymmetricGammaFactor F ψ ν π I(z) (rationalEpsilonMonomial (c^(n+2) (∏ z_i)^m) ((n+2) m))`

holds, where `I(z) = Unramified.principalSeriesOfTuple F z`. Then there are a nonzero
`ψ`-Whittaker functional `ℓ` of `π` and a vector `w` of the Whittaker model of `π` for
`ℓ` such that

- `w(g k) = w(g)` for every `g` and every `k ∈ Conductor.levelSubgroup F (n + 2) m`, and
- `w` agrees with the zero-cell function `zeroCellWhittaker` for `ψ` and `ϖ` on the
  mirabolic subgroup (matrices with last row `(0, …, 0, 1)`).

## Proof

1. Genericity gives a nonzero functional `ℓ`, mirabolic restriction injectivity for
   `(π, ℓ)` (module `ZeroCellLift`), and a zero-cell lift `w` (`exists_zeroCellLift`).
   The same applies to `π^ι` with the first dual functional of `ℓ`, which is nonzero and
   `ψ̄`-generic. This gives a vector `v'` whose `π^ι`-Whittaker function is the zero-cell
   function for `ψ̄` on the mirabolic subgroup.
2. Let `Y` be the `ℓ`-Whittaker function of `π^ι(d) v'` for
   `d = diag(ϖ^m I_(n+2), 1)`, and let `C₀ = q^(-N/2) q^N / c^(n+2)` with
   `N = (n+2) m`. Then `C₀ ≠ 0`. The data `(q, ψ, |·|, ϖ, unipotentQuotientHaar)` satisfy
   `Conductor.IsJacquetNormalization`.
3. For every norm-one `z`, on a right half-plane of real `s`, the corank-one integral of
   `U = w - C₀⁻¹ Y` against Jacquet's spherical function `W(·; z; ψ̄)` converges and
   vanishes. The integral of `w` converges and equals `1`, because the integrand equals
   the zero-cell integrand (`corankOneIntegrand_eq_zeroCell`,
   `integrable_integral_corankOneIntegrand_zeroCell`). The integral of `Y` converges and
   equals `C₀` (`forward_corankOne_dualTranslate_eq`, module `EssentialDualIntegral`).
   Linearity uses the Library lemmas `Conductor.CorankOneConverges.sub`,
   `Conductor.CorankOneConverges.smul`, `Conductor.corankOneIntegral_sub` and
   `Conductor.corankOneIntegral_smul`.
4. `U` is invariant under `diag(GL_(n+2)(O), 1)` on `diag(GL_(n+2)(F), 1)`. For `w` this
   follows from `zeroCell_mul_fieldJacquetMirabolic`, and for `Y` from
   `dualTranslate_restriction_invariant`.
5. `eq_zero_on_mirabolic_of_unit_integrals_eq_zero` (module `UnitarySeparation`) shows
   that `U` vanishes on the mirabolic subgroup, and `Conductor.eq_zero_of_mirabolic_eq_zero`
   with mirabolic injectivity shows `U = 0`. So `w = C₀⁻¹ Y`.
6. By `coefficient_dualTranslate_apply`, the dual function of `w` is
   `g ↦ C₀⁻¹ W'(g d)`, where `W'` is the Whittaker function of `v'`. Both `w` and `W'`
   are invariant under the integral row-mirabolic subgroup
   (`mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell`,
   `zeroCell_mul_fieldJacquetMirabolic`). The Library theorem
   `Conductor.mem_levelFixedVectors_of_rankInclusion_dual_comparison`, the Library form of
   JPSS (5.3), then puts `w` in the level-`m` fixed space.

The main theorem needs `set_option maxHeartbeats 1000000`. With the default limit,
elaborating the declaration times out.

## Use

The essential pair input for the highly ramified stability argument applies this theorem
to the twist of a generic representation by a highly ramified character. The gamma
hypothesis comes from the module `UnitaryGamma`.
