# Discrete torus decomposition of the normalized Iwasawa pushforward

`Langlands.RankinSelberg.iwasawaTorusSum :
IwasawaTorusSumStatement.{uF}` proves the published closed proposition from
`Langlands.Representation.RankinSelberg.IwasawaTorusSumStatement`. The universe
`uF` is arbitrary. The theorem preserves every prime `p`, field
`F : PadicField.{uF} p`, supplied realization `T : F.TopologicalData`, natural
`n`, uniformizing element `ϖ` and integer exponent vector. All helper results
in this module are private.

For `m = n + 1`, write `A = Fin m → F.Carrierˣ`,
`G = Langlands.GeneralLinear m F.Carrier`,
`Q = LeftUnipotentQuotient n F.Carrier`, and
`K = Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`.
The theorem uses the statement's actual measures
`da = Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)` and
`dk = (generalLinearHaar F.Carrier n).restrict K`, the ordinary diagonal
coordinates, and the maps
`q(a,k) = [Iwasawa.diagonalUnits a * k]`,
`t(λ)_i = ϖ ^ λ_i`, and `qLam(λ)(k) = [Iwasawa.torus ϖ λ * k]`.
With `δ(a) = ∏_{i<j} T.normalizedAbs(a_i/a_j)`, the proved identity is

```text
Measure.map q ((da.prod dk).withDensity
    (fun (a,k) => ENNReal.ofReal (δ(a)⁻¹))) =
  Measure.sum (fun λ : Fin m → ℤ =>
    ENNReal.ofReal (δ(t λ)⁻¹) • Measure.map (qLam λ) dk).
```

The sum includes every integer exponent vector. The scalar is exactly one.
At rank one, the modulus is the empty product and equals one.

The proof first applies the published `iwasawaTorusPartition` at rank `m`.
For the integral-unit box
`U = {u : A | ∀ i, u i ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer}`,
this gives a countable measurable partition by
`C λ = (fun u => t λ * u) '' U`. It supplies `da U = 1`, mass one for every
stratum, pairwise disjointness, exhaustive covering, and the exact identity

```text
Measure.map (fun u => t λ * u) (da.restrict U) = da.restrict (C λ).
```

That imported result proves the partition from the uniformizer's existence
and uniqueness properties and the published normalization
`localMultiplicativeHaar_integerUnits`. Its countable coset cover supplies
sigma-finiteness for the product-measure calculation. This module uses the
proved partition without adding any hypothesis to the final theorem.

The private `normalizedAbs_integralUnit` uses the published
`valuation_eq_one_of_mem_integralUnits` and
`T.normalizedAbs_eq_one_iff_discreteValuation` to show that integral units
have normalized absolute value one. Multiplicativity then gives
`modulus_integralUnit_shift`: each ratio in the product has unchanged
absolute value under `a ↦ a * u` for `u ∈ U`. Thus
`δ(t λ * u) = δ(t λ)` on each stratum.

For the compact factor, `restrictedHaar_mul_left` proves that left
translation by any element of a measurable subgroup preserves ambient
left Haar restricted to that subgroup. It combines `Measure.restrict_map`,
the subgroup preimage identity and `map_mul_left_eq_self`.
`restrictedHaar_absorb` transports this invariance through a measurable
map after a fixed left factor. For `u ∈ U`, the published
`Iwasawa.diagonalUnits_mem` and valuation-one lemma give
`Iwasawa.diagonalUnits u ∈ K`. The diagonal homomorphism law gives

```text
q(t λ * u,k) = qLam(λ)(Iwasawa.diagonalUnits u * k).
```

Consequently the pushforward in the `k` variable is the fixed measure
`Measure.map (qLam λ) dk` throughout the stratum.

The generic private `weighted_partition_pushforward` proves the measure
identity by evaluating both sides on an arbitrary measurable set `s`.
Its indicator composed with `q` is measurable. Tonelli rewrites the
weighted product integral as the outer integral of
`w(a) * ∫⁻ k, s.indicator 1 (q(a,k)) ∂dk`.
`Measure.restrict_iUnion` expresses `da` as the sum of its restrictions to
the disjoint strata, and `lintegral_sum_measure` decomposes that integral.
The restricted-measure translation identity changes each summand to an
integral over `U`. Constancy of the weight and of the fiberwise pushforward,
together with `da U = 1`, gives
`w(t λ) * Measure.map (qLam λ) dk s`. The sum of these values is exactly
the right-hand measure evaluated at `s`. All integrals are nonnegative
extended integrals, so infinite values require no convergence or
integrability assumption. The generic argument only needs the inner
measure to be s-finite.

The application `iwasawaTorusSum_from_partition` establishes those
measurability and finiteness inputs. The published
`GeneralLinear.continuous_diagonalUnits`, imported from `UpperBruhatCells`,
provides continuity using the entries of the diagonal matrix and its inverse.
Continuity of the quotient map makes `q` measurable. The normalized
absolute value is continuous; each diagonal ratio is continuous and has
positive absolute value. Finite products and inversion therefore make
the inverse-modulus weight measurable. The actual compact subgroup is
measurable because it equals the level-zero open subgroup.
`generalLinearHaar_integralSubgroup` gives `dk Set.univ = 1`, hence `dk`
is finite and s-finite. The final theorem installs the statement's
supplied instances and applies this assembly to `iwasawaTorusPartition`.

This is an internal derived proof of the internal measure identity
described in the target's Markdown. Its provenance is the published
`RankinSelberg.Measures` normalizations, the diagonal and torus
constructions in `Whittaker.Iwasawa`, the local-field normalized
absolute-value laws and Mathlib's map, restriction, measure sum, density
and nonnegative product-integral results. The imported
`PadicScalarHaarScalingProof` provides the proved second countability of
the supplied topology used for Borel product measurability. The proof
constructs no compatible quotient measure and uses no full quotient
Iwasawa integration formula or theorem assuming that formula.
