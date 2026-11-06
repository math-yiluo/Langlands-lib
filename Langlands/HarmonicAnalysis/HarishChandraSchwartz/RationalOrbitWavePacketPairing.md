# The pairing of a coefficient with a wave packet (Proposition VII.2.1, `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralInversion` (Worker 249,
  published as candidate `81fd7d32`): `rationalOrbitCentralCharacter` (the restriction `χ_ω` to
  `A_G` of the central character of `ω`), `rationalOrbitCentralCharacter_orbitMap`,
  `integral_rationalOrbitCentralInversion` and `integral_rationalOrbitCentralInversion_eq_zero`;
  through its imports `rationalOrbitInversionIntegrand`, `finite_setOf_unitaryUnramifiedCharacter_mul_eq`,
  `unitaryUnramifiedCharacter_apply_of_mem`, the orbit `discreteSeriesOrbit`, the orbit map
  `discreteSeriesOrbitMap` with `isOpenQuotientMap_discreteSeriesOrbitMap`, the I.1 orbit
  measure `rationalNormalizedDiscreteSeriesOrbitMeasure`, `discreteSeriesCentralRestriction`
  and `continuous_discreteSeriesCentralRestriction` (Worker 200);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient`: the central projection
  `centralProjection` and `integral_centralProjection_mul_conj`
  (`∫_{A\G} (p_χ φ)(q̇) conj(K(q̇)) dν(q) = ∫_G conj(K) φ dμ_G` for `χ`-covariant `K`), with the
  quotient-measure compatibility `IsCompatible` of `Langlands.Analysis.Local.QuotientMeasure`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.HermitianSchurOrthogonality` (Worker 249):
  `hermitianCoefficientIntegrand`, `hermitianCoefficientPairing`,
  `integrable_hermitianCoefficientIntegrand`, `hermitianCoefficientPairing_eq_zero`,
  `hermitianCoefficientPairing_eq_inner`, `isUnitarizable_of_isSquareIntegrable`, and through
  its imports `coefficientTensorMap`, `coefficientTensorMap_mul_of_central`,
  `coefficientTensorInvariantForm` and `formalDegree`;
- `Langlands.Representation.Plancherel.DiscreteSeriesFormalDegree`: the formal degree
  `discreteSeriesFormalDegree` of a discrete-series class and
  `discreteSeriesFormalDegree_eq_formalDegree`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction`:
  `CompactOpenSubgroup.cofinal` (every open subgroup contains a compact open subgroup, given a
  compact open subgroup);
- `Langlands.Analysis.Local.NormalSubgroupHaarModulus` (Worker 1423):
  `normalLeftQuotientHomeomorph A : A\G ≃ₜ G/A` for a normal subgroup `A`;
- for the local instances on `G(F)`: `Langlands.GroupScheme.Rational.PointTopology`
  (`rationalPointTopology`, `rationalPoints_nonarchimedeanGroup`, `rationalPoint_t2Space`,
  `rationalPoint_locallyCompactSpace`), `Langlands.GroupScheme.AffinePointFiniteCoordinates`
  and `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof` (second countability, as in
  `RationalPointCentralCharacter`), and `Langlands.BruhatTits.Unipotent.RationalPointCompactOpen`
  (`BruhatTits.rationalPointCompactOpenSubgroup`, `BruhatTits.localField_t2Space`).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- VI.3, printed p. 302 (PDF p. 68): "Pour `ψ ∈ C^∞(O, P)` définissons une fonction `f_ψ` sur
  `G` par `f_ψ(g) = ∫_O µ(ω) (E^G_P ψ_ω)(g) dω`", where `O` carries the measure for which
  `Im X(M) → O`, `χ ↦ ω ⊗ χ`, preserves measures locally. V.2, printed p. 292 (PDF p. 58):
  `µ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`, `α` running over the reduced roots of `A_M` up to sign.
- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84): for
  `ψ' ∈ E' ⊗ Ě'`, "`(E^G_G ψ', f_ψ)_G = ∫_G conj((E^G_G ψ')(g)) f_ψ(g) dg =
  ∫_{A_G\G} conj((E^G_G ψ')(g)) ϕ(g) dg`, où `ϕ(g) = ∫_{A_G} f_ψ(ag) χ_{ω'}(a⁻¹) da`" (the
  printed overbars on `(E^G_G ψ')(g)` in both integrals are written `conj`); after the Fourier
  inversion
  `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`, "D'où l'égalité `(E^G_G ψ', f_ψ)_G =
  ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ', E^G_G ψ_ω)_{A_G\G}`. Des formules analogues à III.1 (2) et
  (3) (pour des produits hermitiens) impliquent que `(E^G_G ψ', E^G_G ψ_ω)_{A_G\G}` = `0`, si
  `ω' ≄ ω`, `(ψ', ψ_ω)`, si `ω' ≃ ω`. On obtient `(E^G_G ψ', f_ψ)_G` = `0`, si `ω' ∉ O`,
  `(ψ', ψ_{ω'})`, si `ω' ∈ O`."
- Conventions: Hermitian products are antilinear in the first variable (V.2, printed p. 293,
  PDF p. 59), so `(f₁, f₂)_X = ∫_X conj(f₁) f₂`. On `L(ω, G) = E ⊗ Ě`,
  `(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)` for a positive definite invariant product on
  `E` and the induced product on `Ě` (V.2, printed p. 293, PDF p. 59), with `d(ω)` the formal
  degree of III.1 (3).

This module formalizes these steps for `M = G`. The generic theorem, the lemmas on chosen
representatives and on `A\G`, and the finite-sum form of the Fourier inversion are derived for
the proof; `rationalOrbitWavePacket` is Waldspurger's `f_ψ` for `M = G` with the section `ψ`
read through chosen representatives (see below).

### Correspondence with the source

- For `M = G` there are no reduced roots of `A_G`, and `j(ω) = ∏_α j_α(ω)` (IV.3 (5)) is an
  empty product, so `µ(ω) = 1` and `f_ψ(g) = ∫_O (E^G_G ψ_ω)(g) dω`. The orbit `O` of
  `ω₀ = omega` is `discreteSeriesOrbit`, with the measure
  `rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega`.
- Waldspurger's `ψ_ω ∈ L(ω, G) = E_ω ⊗ Ě_ω` lives on a realization `E_ω` of `ω`, with the
  canonical identifications of VI.1 between equivalent realizations. Here every class `ω`
  has the chosen representative `Quotient.out ω`, and `ψ` is a section assigning to each `ω ∈ O`
  a `CoefficientTensor` of that representative; `(E^G_G ψ_ω)(g)` is
  `coefficientTensorMap _ (ψ ω) g`. No smoothness of `ψ` is assumed; only the continuity of
  `ω ↦ (E^G_G ψ_ω)(g)` for every `g` enters, as the hypothesis `hcont`. Likewise `ω'` is a
  discrete-series class and `ψ'` a coefficient tensor of its chosen representative.
- The pairing on `A_G\G`, `(E^G_G ψ', E^G_G ψ_ω)_{A_G\G}`, is written
  `∫ q, conj ((E ψ')(q̇)) (E ψ_ω)(q̇) ∂ν` with `q̇ = Quotient.out q`, for a measure `ν` on the
  left quotient `A_G\G(F)` that is compatible with `μ_G` and `μ_A` (`IsCompatible`, the Lean
  form of `dg = da dq`) and whose image under `A_G\G ≃ₜ G/A_G` is the Haar measure `mu` used for
  square integrability and for `d(ω)`.
- `(ψ', ψ_{ω'})` is `d(ω')⁻¹ (ψ', ψ_{ω'})_b`, where `d(ω') = discreteSeriesFormalDegree … ω'`
  and `( , )_b` is `coefficientTensorInvariantForm … b`, the product
  `(v₂ ⊗ ℓ₂, v₁ ⊗ ℓ₁) = b(v₂, v₁)(ℓ₂, ℓ₁)` on `E' ⊗ Ě'` induced by a positive invariant form `b`
  on `E'`, as in V.2.
- The Fourier inversion is the one of `RationalOrbitCentralInversion`: the factor
  `μ_A(A_G ∩ G¹)` is kept (Waldspurger normalizes `mes(A_G ∩ K) = 1`, I.1) and the case
  distinction is by restriction to `A_G ∩ G¹` instead of `A_G ∩ K`; in the combined form
  `integral_rationalOrbitCentralInversion_eq_finsum` both cases are one formula, the sum being
  empty when the restrictions differ.

## Scope and hypotheses

### Generic section

`G` a topological group, `T2Space`, `LocallyCompactSpace`, `SecondCountableTopology`, with a
measurable structure and `BorelSpace`; `A` a subgroup with `hA : IsClosed (A : Set G)`, with
measurable structures and `BorelSpace` on `A` and on `LeftQuotient A`; `μA` on `A` `SFinite`,
right invariant and finite on compacts; `μG` on `G` finite on compacts; `ν` a measure on
`LeftQuotient A`; `O` a measurable space with a measure `ρ`.

- `integral_conj_mul_integral_eq_finsum hA ρ hν hη hK he hint hS hinv hintS`: in addition
  `[MeasurableMul A]`; `hν : IsCompatible A μG μA ν`; `eta : A →* Circle` with
  `hη : Measurable fun a => (eta a : ℂ)`; `K : G → ℂ` with `hK : K(a g) = eta(a) K(g)`;
  `e : O → G → ℂ` and `cc : O → A →* Circle` with `he : e ω (a g) = cc(ω)(a) e ω g`;
  `hint`: `g ↦ conj(K g) ∫_O e ω g dρ` is `μG`-integrable; `c : ℂ`, `S : Set O` with
  `hS : S.Finite`; `hinv`: for every `g`,
  `∫_A eta(a⁻¹) ∫_O e ω g cc(ω)(a) dρ dμA = c ∑ᶠ_{ω ∈ S} e ω g`; `hintS`: for `ω ∈ S`,
  `q ↦ conj(K q̇) e ω q̇` is `ν`-integrable.

### Representatives section

`G` a topological group, `A` a normal subgroup with `hA : A ≤ Subgroup.center G`, a measurable
structure on `G/A` with a Haar measure `μ`.

- `isSquareIntegrableModCentralSubgroup_out A hA μ ω`, `discreteSeriesClass_out A hA μ ω`,
  `out_representation_central A hA μ ω a v`, `out_representation_central_of_eq A hA μ hη a v`
  (`hη : χ_{ω₁} = η`), `coefficientTensorMap_out_mul A hA μ ω ψ a g`: no further hypotheses.
- `eq_of_out_equiv e`: `G` a group with a topology (no topological group structure needed),
  `ω₁ ω₂` classes of irreducible admissible representations, `e` an equivalence of their chosen
  representatives.

### Left quotient section

`G` a topological group, `A` a normal subgroup, measurable structures and `BorelSpace` on `G/A`
and `LeftQuotient A`, `μ` on `G/A`, `ν` on `LeftQuotient A`, `χ : A →* ℂˣ`, smooth
representations `P₁`, `P₂` on which `A` acts by `χ` (`h₁`, `h₂`), `hu : ∀ a, ‖χ a‖ = 1`.

- `hermitianCoefficientIntegrand_normalLeftQuotientHomeomorph A h₁ h₂ hu ψ₂ ψ₁ q`: no measure
  hypotheses.
- `integrable_leftQuotient_of_hermitianCoefficientIntegrand A μ hνμ h₁ h₂ hu ψ₂ ψ₁ h`:
  `hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ` and `h`: the Hermitian integrand is
  `μ`-integrable.
- `integral_leftQuotient_eq_hermitianCoefficientPairing A μ hνμ h₁ h₂ hu ψ₂ ψ₁`: `μ` Haar and
  inversion invariant, and `hνμ`.

### Class pairing section

`G` a topological group, `A` normal with `hA : A ≤ Subgroup.center G`, measurable structure and
`BorelSpace` on `G/A`, `μ` Haar and inversion invariant, `hcof`: every open subgroup contains a
compact open subgroup, measurable structure and `BorelSpace` on `LeftQuotient A`, `ν` with
`hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ`.

- `discreteSeriesFormalDegree_eq_formalDegree_out A hA μ hcof ω`: no further hypotheses (no `ν`).
- `integrable_conj_mul_out A hA μ hcof hνμ hω ψ₂ ψ₁`: `hω : χ_{ω₁} = χ_{ω₂}` on `A`.
- `integral_conj_mul_out_eq_zero A hA μ hcof hνμ hω hne ψ₂ ψ₁`: `hω` and `hne : ω₁ ≠ ω₂`.
- `integral_conj_mul_out_self A hA μ hcof hνμ ω b ψ₂ ψ₁`: `b` a positive invariant form on the
  chosen representative of `ω`.

### Rational section

`F` a nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
`IsNonarchimedeanLocalField`); `G` an affine group scheme over `F` locally of finite type. Local
instances give `G(F)` the canonical rational-point topology, the nonarchimedean topological
group structure, `T2Space`, `LocallyCompactSpace`, `SecondCountableTopology`, and a compact open
subgroup, so that `CompactOpenSubgroup.cofinal` supplies `hcof`. `T` an affine commutative group
scheme, `s : T → G` with `hs : GroupScheme.IsCentral s`, `A_G = s(T(F))`, a measurable structure
on `G(F)/A_G` with a measure `mu`, and `hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.

- `finite_setOf_rationalOrbitCentralCharacter_eq s hs mu hindex omega eta`: `mu` Haar, `omega` a
  discrete-series class, `eta : A_G →* Circle`.
- `integral_rationalOrbitCentralInversion_eq_finsum s hs mu hindex hG omega ν eta hΦ hint`:
  `hG : GroupScheme.IsConnectedReductive G`, `mu` Haar, a measurable structure with
  `BorelSpace` on `A_G`, `ν` left invariant on `A_G`, `hΦ : Continuous Φ` for
  `Φ : O → ℂ`, and `hint`: the orbit integrand `rationalOrbitInversionIntegrand … χ eta Φ` is
  `ν`-integrable.
- `rationalOrbitWavePacket s hs mu hindex omega ψ` and `rationalOrbitWavePacket_apply`: `mu`
  Haar, `omega`, and the section `ψ`.

The three pairing theorems further assume measurable structures with `BorelSpace` on `G(F)`,
`A_G` and `A_G\G(F)`, and `BorelSpace` on `G(F)/A_G`. Each of
`integral_conj_mul_rationalOrbitWavePacket s hs mu hindex hG hAc omega μA μG ν hν hνμ ψ hcont
hintA omega' ψ' hint`, `integral_conj_mul_rationalOrbitWavePacket_eq_zero … hintA omega'
homega' ψ' hint` and `integral_conj_mul_rationalOrbitWavePacket_of_mem … hintA omega' homega' b
ψ' hint` takes:

- `hG : GroupScheme.IsConnectedReductive G`;
- `hAc : IsClosed (A_G : Set G(F))`;
- `mu` Haar and inversion invariant;
- `omega`, a discrete-series class (square integrable modulo `A_G` for `mu`);
- `μA` on `A_G`: `SFinite`, left invariant, right invariant, finite on compacts;
- `μG` on `G(F)`: finite on compacts;
- `ν` on `A_G\G(F)` with `hν : IsCompatible A_G μG μA ν` and
  `hνμ : ν.map (normalLeftQuotientHomeomorph A_G) = mu`;
- the section `ψ` with `hcont`: for every `g`, `ω ↦ (E^G_G ψ_ω)(g)` is continuous on `O`;
- `hintA`: for every `g`, `a ↦ f_ψ(a g)` is `μA`-integrable;
- `omega'` a discrete-series class and `ψ'` a coefficient tensor of its chosen representative;
- `hint`: `g ↦ conj((E^G_G ψ')(g)) f_ψ(g)` is `μG`-integrable;

and in addition `homega' : omega' ∉ O` for `_eq_zero`, and `homega' : omega' ∈ O` and a
positive invariant form `b` on the chosen representative of `ω'` for `_of_mem`.

## Definitions

- `rationalOrbitWavePacket s hs mu hindex omega ψ g = ∫_O (E^G_G ψ_ω)(g) dω` for the orbit
  measure `rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega`, i.e. `f_ψ(g)`.

## Results

- `integral_conj_mul_integral_eq_finsum`:
  `∫_G conj(K g) ∫_O e ω g dρ dμG = c ∑ᶠ_{ω ∈ S} ∫_{A\G} conj(K q̇) e ω q̇ dν(q)`.
- `isSquareIntegrableModCentralSubgroup_out`: the chosen representative of a discrete-series
  class is square integrable modulo `A`; `discreteSeriesClass_out`: its class is `ω`.
- `out_representation_central`: `A` acts on the chosen representative of `ω` by `χ_ω`;
  `out_representation_central_of_eq`: by `η` if `χ_ω = η`.
- `eq_of_out_equiv`: classes with equivalent chosen representatives are equal.
- `coefficientTensorMap_out_mul`: `(E ψ)(a g) = χ_ω(a) (E ψ)(g)` for `a ∈ A`.
- `hermitianCoefficientIntegrand_normalLeftQuotientHomeomorph`: the Hermitian integrand on
  `G/A` at the image of `q ∈ A\G` is `conj((E ψ₂)(q̇)) (E ψ₁)(q̇)`.
- `integrable_leftQuotient_of_hermitianCoefficientIntegrand` and
  `integral_leftQuotient_eq_hermitianCoefficientPairing`: integrability and integral of
  `q ↦ conj((E ψ₂)(q̇)) (E ψ₁)(q̇)` on `A\G` are those of the Hermitian integrand on `G/A`; the
  integral is `hermitianCoefficientPairing`.
- `discreteSeriesFormalDegree_eq_formalDegree_out`: `d(ω)` is the formal degree of the chosen
  representative of `ω`.
- `integrable_conj_mul_out`: for `χ_{ω₁} = χ_{ω₂}`, `q ↦ conj((E ψ₂)(q̇)) (E ψ₁)(q̇)` is
  `ν`-integrable.
- `integral_conj_mul_out_eq_zero` (Hermitian III.1 (2) on `A\G`): for `χ_{ω₁} = χ_{ω₂}` and
  `ω₁ ≠ ω₂`, `∫_{A\G} conj((E ψ₂)(q̇)) (E ψ₁)(q̇) dν(q) = 0`.
- `integral_conj_mul_out_self` (Hermitian III.1 (3) on `A\G`):
  `∫_{A\G} conj((E ψ₂)(q̇)) (E ψ₁)(q̇) dν(q) = d(ω)⁻¹ (ψ₂, ψ₁)_b`.
- `finite_setOf_rationalOrbitCentralCharacter_eq`: `{ω ∈ O | χ_ω = η}` is finite.
- `integral_rationalOrbitCentralInversion_eq_finsum`:
  `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = ν(A_G ∩ G¹) ∑ᶠ_{ω ∈ O ; χ_ω = η} Φ(ω)`, without a
  condition on `η`.
- `rationalOrbitWavePacket_apply`: the defining formula.
- `integral_conj_mul_rationalOrbitWavePacket`:
  `∫_G conj((E^G_G ψ')(g)) f_ψ(g) dμG(g) = μA(A_G ∩ G¹) ∑ᶠ_{ω ∈ O ; χ_ω = χ_{ω'}}
  ∫_{A_G\G} conj((E^G_G ψ')(q̇)) (E^G_G ψ_ω)(q̇) dν(q)`.
- `integral_conj_mul_rationalOrbitWavePacket_eq_zero`: if `ω' ∉ O`, this integral is `0`.
- `integral_conj_mul_rationalOrbitWavePacket_of_mem`: if `ω' ∈ O`, it is
  `μA(A_G ∩ G¹) d(ω')⁻¹ (ψ', ψ_{ω'})_b`.

Here `A_G ∩ G¹` is `Subtype.val ⁻¹' rationalCommonNormKernel G`.

## Proof notes

1. Generic theorem: with `χ = Circle.toUnits ∘ eta` (unitary by `hη`),
   `integral_centralProjection_mul_conj` rewrites `∫_G conj(K) f` as
   `∫_{A\G} (p_χ f)(q̇) conj(K(q̇)) dν`; `he` and `hinv` give `(p_χ f)(g) = c ∑_{ω ∈ S} e ω g`;
   the finite sum is exchanged with the integral by `integral_finsetSum` and `hintS`.
2. Representatives: `Quotient.out_eq` and `discreteSeriesUnitaryCentralCharacter_acts`;
   `coefficientTensorMap_out_mul` is `coefficientTensorMap_mul_of_central` with `a g = g a`
   (`A` central); `eq_of_out_equiv` is `Quotient.out_equiv_out` with `SmoothRep.mkIso`.
3. Left quotient: `normalLeftQuotientHomeomorph A q` is the coset of `q̇`, so the Hermitian
   integrand there is the stated function (`Quotient.out_eq`); integrability and integrals
   transfer through `hνμ` and the measurable embedding of the homeomorphism.
4. Class pairing: `discreteSeriesFormalDegree_eq_formalDegree_out` rewrites `ω` as the class of
   its chosen representative and applies `discreteSeriesFormalDegree_eq_formalDegree`. The
   other three combine step 3 with `integrable_hermitianCoefficientIntegrand` (unitarizability
   from `isUnitarizable_of_isSquareIntegrable`), `hermitianCoefficientPairing_eq_zero` (no
   equivalence between the representatives, by `eq_of_out_equiv` and `hne`) and
   `hermitianCoefficientPairing_eq_inner`.
5. Finiteness: every `ω ∈ O` is `χ ω₀` for some `χ ∈ Im X(G)` (surjectivity of the orbit map);
   `χ_{χ ω₀} = η` means `χ χ_{ω₀} = η` on `A_G` (`rationalOrbitCentralCharacter_orbitMap`), and
   such `χ` form a finite set (`finite_setOf_unitaryUnramifiedCharacter_mul_eq`).
6. Combined inversion: if `η = χ_{ω₀}` on `A_G ∩ G¹`, this is
   `integral_rationalOrbitCentralInversion`; otherwise `integral_rationalOrbitCentralInversion_eq_zero`
   gives `0` and the set `{χ_ω = η}` is empty, since `χ ∈ Im X(G)` is trivial on `G¹`
   (`unitaryUnramifiedCharacter_apply_of_mem`), so `χ_{χ ω₀} = χ_{ω₀}` on `A_G ∩ G¹`.
7. Pairing: step 1 with `K = E^G_G ψ'` (covariant by `χ_{ω'}`, step 2), `e(ω) = E^G_G ψ_ω`,
   `cc = χ_•`, `S = {ω ∈ O | χ_ω = χ_{ω'}}` (step 5), `c = μA(A_G ∩ G¹)`, `hinv` from step 6 with
   `Φ = (ω ↦ (E^G_G ψ_ω)(g))` (continuous by `hcont`; the integrand is integrable because it is
   `a ↦ χ_{ω'}(a⁻¹) f_ψ(a g)` by step 2, bounded times `hintA`), and `hintS` from
   `integrable_conj_mul_out`.
8. Off the orbit, every `ω ∈ S` differs from `ω'` (as `ω ∈ O`), so each term vanishes by
   `integral_conj_mul_out_eq_zero`. On the orbit, the finite sum is over a finset containing
   `ω'`; the other terms vanish by `integral_conj_mul_out_eq_zero` and the term `ω'` is
   `integral_conj_mul_out_self`.

## Open obligations

- The hypotheses `hintA` and `hint` are not stated by Waldspurger; they rest on
  `f_ψ ∈ C(G)` (Proposition VI.3.1) and the bound of coefficients of `ω'` by a multiple of `Ξ`,
  neither of which is used here.
- The hypothesis `hcont` comes in the source from `ψ ∈ C^∞(O, G)` (Lemma VI.2.1 (i)). The
  Library has `continuous_unitaryOrbitCoefficient` (`ProductInducedOrbitCoefficientSmoothness`,
  Worker 200) for the orbit coefficients of a product-induced discrete series, under all the
  premises listed in that module's Markdown (among them `HasLaurentUnitaryCoordinates ν e` and
  `Continuous e` for the torus coordinates `e`); it is stated for a different model of the
  sections and this module does not use it.
- The normalization `mes(A_G ∩ K) = 1` and the relation between `A_G ∩ K` and `A_G ∩ G¹`.
- The final step of the case `M = G` (comparison with Lemma VII.1.1 (ii) to obtain
  `f̂_ψ(ω') = ψ_{ω'}`) and the general case of Proposition VII.2.1 are not addressed.
