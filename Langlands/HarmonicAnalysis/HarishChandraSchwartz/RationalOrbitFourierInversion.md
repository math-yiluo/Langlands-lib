# Fourier inversion over `A_G` on a discrete-series orbit (Proposition VII.2.1, case `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFourierInversion`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterFourierInversion`
  (submitted with this module): `rationalSplitCenterInversionIntegrand`,
  `integral_rationalSplitCenterInversionIntegrand_eq_zero`,
  `integral_rationalSplitCenterInversionIntegrand`, and through its imports
  `rationalValuationCoordinates`, `rationalUnitaryUnramifiedCharacter_apply` and
  `continuous_torusCharacter`;
- the published `Representation.Plancherel.RationalOrbitIntegration` (Worker 200): the orbit
  integral `rationalDiscreteSeriesOrbitIntegral` and
  `rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral` (the integral over the orbit is
  `|S|⁻¹` times the integral of the pulled-back function over `Im X(G)`), and through its
  imports the orbit `discreteSeriesOrbit`, the stabilizer `discreteSeriesStabilizer`, the orbit
  map `discreteSeriesOrbitMap` with `isOpenQuotientMap_discreteSeriesOrbitMap` and
  `discreteSeriesOrbitHomeomorph`, the I.1 orbit measure
  `rationalNormalizedDiscreteSeriesOrbitMeasure`, `finite_rationalDiscreteSeriesStabilizer`,
  `compactSpace_rationalDiscreteSeriesOrbit`, `finite_rationalUnitaryUnramifiedCharacterRestrict_ker`
  and `mem_rationalUnitaryUnramifiedCharacterRestrict_ker`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84): with
  `ϕ(g) = ∫_{A_G} χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω da`, "La restriction à `A_G ∩ K` de
  `χ_ω` ne dépend pas du point `ω ∈ O`. Si cette restriction est différente de celle de
  `χ_{ω'}`, on a `ϕ(g) = 0`. Supposons ces restrictions égales. Comme la fonction
  `ω ↦ (E^G_G ψ_ω)(g)` est continue, on peut appliquer la formule d'inversion de Fourier. Compte
  tenu des définitions de nos mesures, on obtient `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`."
  Here `χ_π` is the restriction to `A_G` of the central character of `π`.
- VI.3, printed p. 302 (PDF p. 68): `O` carries the measure for which `Im X(M) → O`,
  `χ ↦ ω ⊗ χ`, preserves measures locally; for `M = G` this is
  `rationalNormalizedDiscreteSeriesOrbitMeasure` (its local measure preservation is
  `isLocallyMeasurePreserving_rationalNormalizedDiscreteSeriesOrbitMap`). I.1, printed
  pp. 239–240 (PDF pp. 5–6): the measure on `Im X(G)` and `mes(H ∩ K) = 1`.

This module states the two cases of that step on an actual discrete-series orbit. The finite-sum
lemma and the finiteness lemma are derived for the proof; the integrand is a derived definition
that writes Waldspurger's integrand for an arbitrary function `Φ` on `O`.

### Correspondence with the source

- `A_G` is the image `(GroupScheme.rationalPoints.map s).range` of the rational points of a
  central morphism `s : T → G` (`hs : GroupScheme.IsCentral s`), with an arbitrary Borel
  measurable structure. Discrete series are square integrable modulo this `A_G` for a Haar
  measure `mu` on `G(F)/A_G`, as in `DiscreteSeriesClass`.
- `O` is the orbit `discreteSeriesOrbit … omega` of `ω₀ = omega` under `Im X(G)`, with the I.1
  orbit measure. `P : Im X(G) → O`, `χ ↦ χ ω₀`, is `discreteSeriesOrbitMap`, and
  `S = discreteSeriesStabilizer … omega` is the stabilizer of `ω₀`.
- The Library has no central character attached to a discrete-series class. The restrictions
  `χ_ω` are therefore an explicit function `cc : O → (A_G →* Circle)`, and the twist law
  `hcc : cc(P χ)(a) = χ(a) c(a)` (with `c = χ_{ω₀}`) is a hypothesis. It holds for central
  characters because twisting by `χ` multiplies the central character by `χ`.
- `η = χ_{ω'}` is an arbitrary homomorphism `A_G → Circle`, and `Φ : O → ℂ` an arbitrary
  continuous function, standing for `ω ↦ (E^G_G ψ_ω)(g)` at a fixed `g`.
- The measure `ν` on `A_G` is an arbitrary left invariant measure, and `ν(A_G ∩ G¹)` appears as
  a factor; Waldspurger's normalization `mes(A_G ∩ K) = 1` is not imposed.
- As in `RationalSplitCenterFourierInversion`, the cases are split by the restriction to
  `A_G ∩ G¹` instead of `A_G ∩ K`. By the twist law and the triviality of `Im X(G)` on `G¹`, the
  restriction of `χ_ω` to `A_G ∩ G¹` is that of `c` for every `ω ∈ O`. Equality of `A_G ∩ K` and
  `A_G ∩ G¹` is neither proved nor used.

## Scope and hypotheses

`finsum_mem_preimage_comp` is generic: `α` a group, `H` a finite subgroup, `P : α → β`
surjective (`hPsurj`) with `P x = P y ↔ x⁻¹ y ∈ H` (`hP`), `X ⊆ β` with `P⁻¹(X)` finite (`hfin`),
`Φ : β → ℂ` arbitrary.

In the rest, `F` is a nonarchimedean local field (`IsNonarchimedeanLocalField`), `G` an affine
group scheme over `F` locally of finite type with `G(F)` carrying `rationalPointTopology F G.X`,
`T` an affine commutative group scheme over `F`, `s : T → G` with `hs : GroupScheme.IsCentral s`,
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`, a measurable space on
`G(F)/A_G` and a measure `mu` on it.

- `finite_setOf_unitaryUnramifiedCharacter_mul_eq s hs hindex c eta`: `hs`, `hindex`, `G`
  affine (not locally of finite type), `c`, `eta` arbitrary.
- `rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ a`: `mu` a Haar measure
  (`Measure.IsHaarMeasure mu`), `omega` a discrete-series class; no further hypotheses.
- `rationalOrbitInversionIntegrand_eq s hs mu hindex hG omega cc c eta hcc hΦ a`:
  `hG : GroupScheme.IsConnectedReductive G`, `mu` Haar, the twist law `hcc`, and
  `hΦ : Continuous Φ`.
- `integral_rationalOrbitInversionIntegrand_eq_zero s hs mu hindex hG omega ν cc c eta hcc h hΦ`:
  `hG`, `mu` Haar, a measurable space with `BorelSpace` on `A_G`, `ν` left invariant, `hcc`,
  `h`: some `b ∈ A_G ∩ G¹` has `η(b) ≠ c(b)`, and `hΦ`. No integrability is assumed.
- `integral_rationalOrbitInversionIntegrand s hs mu hindex hG omega ν cc c eta hcc h hΦ hint`:
  `hG`, `mu` Haar, the measurable structure and `ν` as above, `hcc`, `h`: `η(b) = c(b)` for
  every `b ∈ A_G ∩ G¹`, `hΦ`, and `hint`: the orbit integrand is `ν`-integrable.

## Definitions

- `rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ a`
  `= η(a⁻¹) ∫_O Φ(ω) cc(ω)(a) dω`, Waldspurger's `χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω`.

## Results

- `finsum_mem_preimage_comp`: `∑_{x ∈ P⁻¹(X)} Φ(P x) = |H| ∑_{y ∈ X} Φ(y)`.
- `finite_setOf_unitaryUnramifiedCharacter_mul_eq`: `{χ ∈ Im X(G) ; χ c = η on A_G}` is finite.
- `rationalOrbitInversionIntegrand_eq`: the orbit integrand equals `|S|⁻¹` times
  `rationalSplitCenterInversionIntegrand s hs hindex c eta (Φ ∘ P)`.
- `integral_rationalOrbitInversionIntegrand_eq_zero` (**different restrictions**): if `η ≠ c` at
  a point of `A_G ∩ G¹`, then `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = 0`.
- `integral_rationalOrbitInversionIntegrand` (**equal restrictions**):
  `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = ν(A_G ∩ G¹) ∑ᶠ_{ω ∈ O ; χ_ω = η} Φ(ω)`, where
  `ν(A_G ∩ G¹)` is `(ν (Subtype.val ⁻¹' G¹)).toReal` and the sum is finite. With
  `ν(A_G ∩ G¹) = 1` this is Waldspurger's `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`.

## Proof notes

1. `finsum_mem_preimage_comp`: `X = P(P⁻¹ X)` is finite. `Finset.sum_comp` writes the sum over
   `P⁻¹ X` as a sum over `X` of the fibre cardinalities times `Φ`. The fibre over `P x₀` is
   `x₀ H` (`h ↦ x₀ h` is a bijection from `H`), so each cardinality is `|H|`.
2. `finite_setOf_unitaryUnramifiedCharacter_mul_eq`: if `χ₁` is in the set, every `χ` in it
   satisfies `χ = χ₁` on `A_G`. Hence `χ₁⁻¹ χ` lies in the restriction kernel
   (`mem_rationalUnitaryUnramifiedCharacterRestrict_ker`), which is finite, and the set lies in
   the finite range of `k ↦ χ₁ k`.
3. `rationalOrbitInversionIntegrand_eq`: evaluation `χ ↦ χ(a)` on `Im X(G)` is continuous, since
   in the circle coordinates it is `torusCharacter (n a)` (`rationalUnitaryUnramifiedCharacter_apply`,
   `continuous_torusCharacter`). By `hcc`, `cc(·)(a) ∘ P` is `χ ↦ χ(a) c(a)`. Since `P` is a
   quotient map (`isOpenQuotientMap_discreteSeriesOrbitMap`), `ω ↦ cc(ω)(a)` is continuous.
   `rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral`, applied to the bounded continuous
   function `ω ↦ Φ(ω) cc(ω)(a)` on the compact orbit, gives
   `∫_O Φ(ω) cc(ω)(a) dω = |S|⁻¹ ∫_{Im X(G)} Φ(P χ) χ(a) c(a) dχ`.
4. Vanishing: by step 3 and `integral_const_mul` the integral is `|S|⁻¹` times the integral of
   `RationalSplitCenterFourierInversion`, which vanishes.
5. Equal restrictions: by step 3 the integrand on `Im X(G)` is `|S|` times the orbit integrand,
   hence integrable. `integral_rationalSplitCenterInversionIntegrand` (with `f = Φ ∘ P`,
   continuous) gives `ν(A_G ∩ G¹) ∑_{χ ; χ c = η} Φ(P χ)`. By `hcc`, the index set is
   `P⁻¹{ω ; cc ω = η}`, which is finite by step 2. The fibres of `P` are the cosets of `S`
   (`discreteSeriesOrbitHomeomorph` is injective, and `QuotientGroup.eq` applies), and `P` is
   surjective, so step 1 turns the sum into `|S| ∑_{ω ; cc ω = η} Φ(ω)`. The factors `|S|⁻¹` and
   `|S|` cancel.

## Relation to the Library

`RationalSplitCenterFourierInversion` proves the same step with the orbit replaced by `Im X(G)`;
this module transfers it to the orbit through `RationalOrbitIntegration`. No other Library
declaration states Fourier inversion over `A_G` for functions on a discrete-series orbit.

## Open obligations

For Proposition VII.2.1, case `M = G`: a central character map on discrete-series classes with
the twist law (to discharge `hcc`); the normalization `mes(A_G ∩ K) = 1` and its relation to
`ν(A_G ∩ G¹)`; the continuity and integrability, for `ψ ∈ C^∞(O)`, of
`ω ↦ (E^G_G ψ_ω)(g)` and of the orbit integrand; the formula `(E^G_G ψ', f_ψ)_G =
∫_{A_G \ G} (E^G_G ψ')(g) ϕ(g) dg`; the formulas analogous to III.1 (2), (3) for Hermitian
products; and the comparison with Lemma VII.1.1 (ii).
