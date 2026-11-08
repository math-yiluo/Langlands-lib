# The coefficient prime in the completed coefficient rings

This internal module defines the coefficient rings of Harris's `ℓ`-power
stages and proves elementary facts about Harris's coefficient prime
`ℓ` in the completed coefficient rings. For a rational finite place `p`, the
coefficient prime `ℓ = harrisCoefficientPrime p` is the residue
characteristic of `p`. Let `K` be a number field and `l` a place of `K` above
`p`. The module proves that `ℓ` has valuation `< 1` in the completion `K_l`
and is nonzero there. It is a non-unit of the valuation ring `O_l`, and its
powers `ℓ^r` tend to zero in `O_l`. It is also a non-unit of the product
`∏_{l | p} O_l` of the valuation rings at all places above `p`. The module
names the quotient rings `O_l / ℓ^r O_l` and `(∏_{l | p} O_l) / ℓ^r`, and
proves that they are finite, and nonzero for `r ≥ 1`. All declarations are in
namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, works with coefficients modulo powers of the coefficient prime `ℓ`
(printed p. 308) and forms the lisse `ℓ`-adic sheaf from them (printed
p. 311). The module
`Langlands.Shimura.PEL.HarrisTaylorCMEllAdicGaloisCohomology` (candidate
`641dba11-c910-474d-9cbb-3cb23c2b7d20`, accepted and awaiting publication)
specializes the torsion-limit construction at `m = ℓ`. It proves that `ℓ`
lies in every place of `K` above `p`, but not the corresponding facts in
the completed valuation rings. This module supplies them: the coefficients
of the `ℓ`-power stages are taken modulo powers of an element that is a
non-unit of the product of the valuation rings and of each factor, and these
powers tend to zero in each `O_l`.

The module proves no statement about cohomology. In particular it does not
prove that the reductions modulo `ℓ^r` are nonzero for a given coefficient
module, that the ideals `ℓ^r O_l` form a basis of neighbourhoods of zero, or
any comparison of the `ℓ`-power torsion limit with other definitions of
`ℓ`-adic cohomology. No statement of Harris is formalized.

## Inputs

- From `Langlands.Shimura.PEL.HarrisTaylorCMEllAdicGaloisCohomology`
  (candidate `641dba11-c910-474d-9cbb-3cb23c2b7d20`, accepted and awaiting
  publication): `harrisCoefficientPrime`, `harrisCoefficientPrime_ne_zero`
  and `harrisCoefficientPrime_mem_above`.
- From the published `Langlands.Global.Adelic`: `FiniteCompletion K v`, the
  completion `v.adicCompletion K` of `K` at a finite place `v`.
- From the published `Langlands.Global.AdelicFunctoriality`:
  `FinitePlacesAbove K p` and, in `LocalDegree`, the chosen place
  `placeAbove K p` above `p`, which exists because every finite place of `ℚ`
  lies under a finite place of `K`.
- From the published `Langlands.Shimura.Coefficients`:
  `CoefficientIntegers l`, the valuation ring `l.adicCompletionIntegers K`,
  and `HarrisCoefficientIntegers K p`, the product of the rings
  `CoefficientIntegers l.1` over `l : FinitePlacesAbove K p`.
- From the published `Langlands.Shimura.Coefficients.PrincipalReduction`,
  `FiniteReduction` and `HarrisReduction`: the ideals
  `coefficientScalarIdeal l m`, the span of `m` in `CoefficientIntegers l`,
  and `harrisCoefficientScalarIdeal K p m`, the span of `m` in
  `HarrisCoefficientIntegers K p`; the quotient rings
  `CoefficientReductionRing l m n` and `HarrisCoefficientReductionRing K p m n`
  by their `n`-th powers; and their finiteness for `m ≠ 0`,
  `coefficientReductionRing_finite` and
  `harrisCoefficientReductionRing_finite`. These are the ideals by whose
  powers the published torsion coefficient systems are reduced.
- From Mathlib: `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`,
  `valuedAdicCompletion_eq_valuation`,
  `adicCompletionIntegers.isUnit_iff_valued_eq_one`, `tendsto_subtype_rng`,
  `Valued.tendsto_zero_pow_of_v_lt_one`, `Pi.evalRingHom`,
  `Ideal.span_singleton_eq_top`, `Ideal.pow_le_self` and
  `Ideal.Quotient.nontrivial_iff`.

## Declarations

Let `p : Global.FinitePlace ℚ`, let `K` be a number field and let
`l : FinitePlacesAbove K p`. Write `ℓ` for the image of the natural number
`harrisCoefficientPrime p` in the ring at hand.

- `harrisCoefficientPrime_valued_lt_one p l`: `Valued.v ℓ < 1` in
  `FiniteCompletion K l.1`.
- `harrisCoefficientPrime_ne_zero_completion p l`: `ℓ ≠ 0` in
  `FiniteCompletion K l.1`.
- `harrisCoefficientPrime_not_isUnit p l`: `ℓ` is not a unit of
  `CoefficientIntegers l.1`.
- `tendsto_harrisCoefficientPrime_pow p l`: the sequence `ℓ ^ r` tends to
  `0` in `CoefficientIntegers l.1` as `r → ∞`.
- `harrisCoefficientPrime_not_isUnit_integers p`: `ℓ` is not a unit of
  `HarrisCoefficientIntegers K p`.

## The coefficient rings modulo powers of ℓ

Let `r : ℕ`.

- `HarrisEllCoefficientRing p K r` is
  `HarrisCoefficientReductionRing K p (harrisCoefficientPrime p) r`, the ring
  `(∏_{l | p} O_l) / ℓ^r`.
- `HarrisEllPlaceCoefficientRing p l r` is
  `CoefficientReductionRing l.1 (harrisCoefficientPrime p) r`, the ring
  `O_l / ℓ^r O_l`.
- `coefficientScalarIdeal_harrisCoefficientPrime_ne_top p l` and
  `harrisCoefficientScalarIdeal_harrisCoefficientPrime_ne_top p K`: the
  ideals generated by `ℓ` in `O_l` and in the product are proper.
- `harrisEllPlaceCoefficientRing_nontrivial p l hr` and
  `harrisEllCoefficientRing_nontrivial p K hr`: for `r ≠ 0` both rings are
  nontrivial.
- `harrisEllPlaceCoefficientRing_finite p l r` and
  `harrisEllCoefficientRing_finite p K r`: both rings are finite.

## Proof outline

The image of `ℓ` in `𝓞 K` lies in `l.1.asIdeal`, so its `l`-adic valuation
is `< 1`. The valuation on the completion restricts to the `l`-adic
valuation on `𝓞 K`, which gives the first lemma. The image of `ℓ` in `K` is
nonzero because `ℓ ≠ 0` and `K` has characteristic zero, and the map from
`K` to its completion is injective. An element of the valuation ring is a
unit exactly when its valuation is `1`, so `ℓ` is not a unit of `O_l`. Since
the value group is `ℤᵐ⁰`, which is multiplicatively Archimedean, the powers
of an element of valuation `< 1` tend to zero in the completion; the
topology of `O_l` is the subspace topology, so they tend to zero there. A
unit of the product maps to a unit of every factor under evaluation, and the
product has at least the factor at `placeAbove K p`. A principal ideal is the
whole ring exactly when its generator is a unit, so the ideals generated by
`ℓ` are proper. For `r ≠ 0` the `r`-th power of an ideal is contained in the
ideal, hence is proper, and the quotient by a proper ideal is nontrivial.
Finiteness is the published finiteness of the reductions by powers of a
nonzero rational scalar, applied to `ℓ ≠ 0`.

## Provenance

This is an internal module of two abbreviations and elementary facts about valuations, proved from
the published `FiniteCompletion`, `FinitePlacesAbove`, `placeAbove`,
`CoefficientIntegers`, `HarrisCoefficientIntegers` and the published
reductions by scalar ideals, from
`harrisCoefficientPrime_mem_above` of candidate `641dba11`, and from Mathlib.
Harris (1999), printed pp. 308 and 311, is motivation only.
