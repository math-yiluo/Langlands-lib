# The inner product of two wave packets (Proposition VII.2.2 (ii), `M = M' = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketInner`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing` (Worker 249,
  accepted candidate `98f5e360`): the wave packet `rationalOrbitWavePacket` (`f_ψ` for `M = G`)
  with `rationalOrbitWavePacket_apply`, the pairings
  `integral_conj_mul_rationalOrbitWavePacket_eq_zero` and
  `integral_conj_mul_rationalOrbitWavePacket_of_mem` (`(E^G_G ψ', f_ψ)_G`),
  `integral_conj_mul_out_self` (Hermitian III.1 (3) on `A\G`),
  `isSquareIntegrableModCentralSubgroup_out`, `out_representation_central`, and its local
  instances `instRationalOrbitWavePacket1` … `instRationalOrbitWavePacket7` on `G(F)`
  (rational-point topology, nonarchimedean group structure, `T2Space` on `F` and `G(F)`,
  `LocallyCompactSpace`, `SecondCountableTopology`, a compact open subgroup), which this module
  declares as local instances again; through its imports the orbit `discreteSeriesOrbit`,
  `rationalNormCharacters`, the I.1 orbit measure `rationalNormalizedDiscreteSeriesOrbitMeasure`
  with `isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure`,
  `discreteSeriesFormalDegree` with `discreteSeriesFormalDegree_pos`,
  `isUnitarizable_of_isSquareIntegrable`, `coefficientTensorMap`, `coefficientTensorAction`,
  `coefficientTensorInvariantForm` with `coefficientTensorInvariantForm_rescale`,
  `InvariantPositiveForm.rescale` with `InvariantPositiveForm.rescale_inner`,
  `normalLeftQuotientHomeomorph`, `IsCompatible`, `rationalCommonNormKernel` (`G¹`) and
  `CompactOpenSubgroup.cofinal`;
- `Langlands.Representation.Unitary.AdmissibleFormUniqueness`:
  `InvariantPositiveForm.exists_pos_rescale_eq` (two positive invariant forms on an irreducible
  admissible representation differ by a positive scalar).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proposition VII.2.2, printed p. 318 (PDF p. 84): for `ψ ∈ C^∞(O, P)`, `ψ' ∈ C^∞(O', P')`,
  "(ii) Si `M'` est conjugué à `M` dans `G`, on a l'égalité `(f_{ψ'}, f_ψ)_G = γ(G|M) c(G|M)²
  ∑_{s ∈ W(M'|G|M) ; sO = O'} ∫_O µ(ω) (ψ'_{sω}, ⁰c_{P'|P}(s, ω) ψ_ω) dω`."
- Its proof, printed p. 319 (PDF p. 85): "On a l'égalité `(f_{ψ'}, f_ψ)_G = ∫_G ∫_{O'} µ(ω')
  conj((E^G_{P'} ψ'_{ω'})(g)) dω' f_ψ(g) dg`. D'après le Lemme VI.2.2, l'intégrale double est
  absolument convergente. On obtient `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω') (E^G_{P'} ψ'_{ω'}, f_ψ)_G
  dω'`" (the printed overbar on `(E^G_{P'} ψ'_{ω'})(g)` is written `conj`); the proof then
  passes through Lemma VII.1.1 (ii) (formula (1)) and, for `M'` conjugate to `M`, through Lemma
  VII.1.4 and Proposition VII.2.1.
- V.2, printed p. 293 (PDF p. 59): Hermitian products are antilinear in the first variable; for
  a positive definite invariant product on `E` and the induced product on `Ě`,
  "`(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)` … Il ne dépend pas du produit choisi sur `E`
  car, si l'on multiplie celui-ci par `λ > 0`, le produit sur `Ě` est multiplié par `λ⁻¹`."
  For `P = G`, `I^G_G E = E` and the product on it is the one on `E`.

This module formalizes Proposition VII.2.2 (ii) for `M = M' = G` and orbits `O`, `O'` of
discrete series of `G`. The Fubini lemma, the lemmas on the V.2 product and the disjointness of
orbits are derived for the proof. The proof follows Waldspurger's first two steps and then,
instead of passing through `f̂_ψ` (formula (1) and Proposition VII.2.1), uses the pairings
`(E^G_G ψ'_{ω'}, f_ψ)_G` of `RationalOrbitWavePacketPairing` directly, which are the
computation in the proof of Proposition VII.2.1 before its comparison with Lemma VII.1.1 (ii).

### Correspondence with the source

- For `M = M' = G`: `W(G|G|G) = {1}` (`W(M'|G|M) = W^{M'} \ {s ∈ W^G ; s · M ⊂ M'}`, V.1,
  printed p. 288, PDF p. 54, so `W(G|G|G) = W^G \ W^G`); `γ(G|G) = c(G|G) = 1` (printed pp. 240–241, PDF
  pp. 6–7); `⁰c_{G|G}(1, ω)` is the identity (V.3, printed p. 295, PDF p. 61); `µ(ω) = 1`
  (`µ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` over the reduced roots of `A_M`, V.2 printed p. 292; for
  `M = G` there are no roots and `j(ω)` is an empty product, IV.3 (5)). So the right side of (ii)
  is `∫_O (ψ'_ω, ψ_ω) dω` if `O' = O`, and the empty sum `0` otherwise.
- As in `RationalOrbitWavePacketPairing`, a discrete-series class `ω` is read through its chosen
  representative `Quotient.out ω`, a section `ψ` over the orbit `O` of `ω₀ = omega` assigns to
  each `ω ∈ O` a `CoefficientTensor` of that representative, `(E^G_G ψ_ω)(g)` is
  `coefficientTensorMap _ (ψ ω) g`, `f_ψ` is `rationalOrbitWavePacket s hs mu hindex omega ψ`,
  and `O` carries the measure `rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega`.
  Waldspurger's `C^∞(O, G)` is replaced by the hypotheses listed below.
- `(f_{ψ'}, f_ψ)_G` is `∫ g, conj (f_{ψ'}(g)) * f_ψ(g) ∂μG`.
- The product `( , )` on `L(ω, G) = E ⊗ Ě` is `discreteSeriesCoefficientForm … ω`:
  `coefficientTensorInvariantForm` (the product `(v₂ ⊗ ℓ₂, v₁ ⊗ ℓ₁) = b(v₂, v₁)(ℓ₂, ℓ₁)` on
  `E ⊗ Ě` induced by a positive invariant form `b` on `E` and its dual form on `Ě`) rescaled by
  `d(ω)⁻¹`, `d(ω) = discreteSeriesFormalDegree … ω`. The definition uses a chosen `b` (one
  exists by `isUnitarizable_of_isSquareIntegrable`); `discreteSeriesCoefficientForm_eq` is the
  independence of the choice stated in V.2. The Library's `formalDegreeProductForm` and
  `formalDegreeInducedTensorForm` (Worker 200) are the analogous products on induced
  representations from a proper parabolic; this module does not use them.
- Part (ii) for `O' ≠ O` is stated as `omega' ∉ O` for the base point `omega'` of `O'`
  (orbits are equal or disjoint, `notMem_discreteSeriesOrbit_of_mem`). Part (ii) for `O' = O`
  is stated for two sections over the orbit with the same base point `omega`.
- The factor `μA(A_G ∩ G¹)` from the Fourier inversion over `A_G` in
  `RationalOrbitWavePacketPairing` is kept: Waldspurger normalizes `mes(A_G ∩ K) = 1` (I.1), and
  the relation between `A_G ∩ K` and `A_G ∩ G¹` is not used here. Here `A_G ∩ G¹` is
  `Subtype.val ⁻¹' rationalCommonNormKernel G`.

## Scope and hypotheses

### Fubini section

`X`, `Y` measurable spaces with `SFinite` measures `μX`, `μY`.

- `integral_conj_integral_mul_eq_integral_integral e f hint`: `e : Y → X → ℂ`, `f : X → ℂ`,
  `hint`: `(x, y) ↦ conj(e y x) f x` is integrable for `μX.prod μY`.

### Class form section

`G` a topological group, `A` a normal subgroup with `hA : A ≤ Subgroup.center G`, a measurable
structure with `BorelSpace` on `G/A`, `μ` a Haar measure on `G/A` that is inversion invariant,
and `hcof`: every open subgroup of `G` contains a compact open subgroup.

- `coefficientTensorInvariantForm_independent hcof B hB hi b c`: `B` a smooth representation,
  `hB` admissible, `hi` irreducible, `b`, `c` positive invariant forms on `B` (no `A`, `μ`).
- `discreteSeriesCoefficientForm A hA μ hcof ω`: `ω` a discrete-series class (irreducible,
  square integrable modulo `A` for `μ`).
- `discreteSeriesCoefficientForm_eq A hA μ hcof ω b` and
  `discreteSeriesCoefficientForm_inner A hA μ hcof ω b ψ₂ ψ₁`: `b` a positive invariant form on
  the chosen representative of `ω`; `ψ₂`, `ψ₁` coefficient tensors of it.
- `integral_conj_mul_out_self_eq_inner A hA μ hcof hνμ ω ψ₂ ψ₁`: in addition a measurable
  structure with `BorelSpace` on `LeftQuotient A` and `ν` on it with
  `hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ`.

### Rational section

`F` a nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
`IsNonarchimedeanLocalField`); `G` an affine group scheme over `F` locally of finite type, with
the local instances of `RationalOrbitWavePacketPairing` on `G(F)`, so that
`CompactOpenSubgroup.cofinal` supplies `hcof`; `T` an affine commutative group scheme,
`s : T → G` with `hs : GroupScheme.IsCentral s`, `A_G = s(T(F))`, a measurable structure on
`G(F)/A_G` (with `BorelSpace`, except for `notMem_discreteSeriesOrbit_of_mem`) and a measure
`mu` on it, and `hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.

- `rationalOrbitSectionInner s hs mu hindex omega ψ' ψ` and `rationalOrbitSectionInner_apply`:
  `mu` Haar and inversion invariant, `omega` a discrete-series class, `ψ'`, `ψ` sections over its
  orbit `O`.
- `notMem_discreteSeriesOrbit_of_mem s hs mu homega' hω`: `mu` Haar (`T` need not be affine);
  `homega' : omega' ∉ O` (the orbit of `omega`) and `hω : ω ∈ O'` (the orbit of `omega'`).

The two main theorems further assume measurable structures with `BorelSpace` on `G(F)`, `A_G`
and `A_G\G(F)`. Each of
`integral_conj_rationalOrbitWavePacket_mul_eq_zero s hs mu hindex hG hAc omega μA μG ν hν hνμ ψ
hcont hintA omega' homega' ψ' hint` and
`integral_conj_rationalOrbitWavePacket_mul s hs mu hindex hG hAc omega μA μG ν hν hνμ ψ hcont
hintA ψ' hint` takes:

- `hG : GroupScheme.IsConnectedReductive G`;
- `hAc : IsClosed (A_G : Set G(F))`;
- `mu` Haar and inversion invariant;
- `omega`, a discrete-series class (square integrable modulo `A_G` for `mu`), with orbit `O`;
- `μA` on `A_G`: `SFinite`, left invariant, right invariant, finite on compacts;
- `μG` on `G(F)`: finite on compacts;
- `ν` on `A_G\G(F)` with `hν : IsCompatible A_G μG μA ν` and
  `hνμ : ν.map (normalLeftQuotientHomeomorph A_G) = mu`;
- the section `ψ` over `O` with `hcont`: for every `g`, `ω ↦ (E^G_G ψ_ω)(g)` is continuous on
  `O`, and `hintA`: for every `g`, `a ↦ f_ψ(a g)` is `μA`-integrable;

and in addition:

- for `_eq_zero`: a discrete-series class `omega'` with `homega' : omega' ∉ O`, a section `ψ'`
  over the orbit `O'` of `omega'`, and `hint`: `(g, ω') ↦ conj((E^G_G ψ'_{ω'})(g)) f_ψ(g)` is
  integrable on `G(F) × O'` for `μG` times the orbit measure of `O'`;
- for the same-orbit theorem: a section `ψ'` over `O`, and `hint`:
  `(g, ω) ↦ conj((E^G_G ψ'_ω)(g)) f_ψ(g)` is integrable on `G(F) × O` for `μG` times the orbit
  measure of `O`.

## Definitions

- `discreteSeriesCoefficientForm A hA μ hcof ω`: the positive invariant form
  `d(ω)⁻¹ (·, ·)_b` on `coefficientTensorAction` of the chosen representative of `ω`, for a
  chosen positive invariant form `b` (the product of V.2 for `P = G`).
- `rationalOrbitSectionInner s hs mu hindex omega ψ' ψ = ∫_O (ψ'_ω, ψ_ω) dω`, the product of V.2
  of `ψ' ω` and `ψ ω` integrated for the orbit measure of `O`; this is the right side of
  Proposition VII.2.2 (ii) for `M = M' = G` and `O' = O`.

## Results

- `integral_conj_integral_mul_eq_integral_integral`:
  `∫_X conj(∫_Y e y x dμY) f x dμX = ∫_Y ∫_X conj(e y x) f x dμX dμY`.
- `coefficientTensorInvariantForm_independent`: on an irreducible admissible representation the
  form `(·, ·)_b` on coefficient tensors is the same for all positive invariant forms `b`.
- `discreteSeriesCoefficientForm_eq`: `discreteSeriesCoefficientForm … ω` is `d(ω)⁻¹ (·, ·)_b`
  for every positive invariant form `b`; `discreteSeriesCoefficientForm_inner`: its value on
  `ψ₂`, `ψ₁` is `d(ω)⁻¹ (ψ₂, ψ₁)_b`.
- `integral_conj_mul_out_self_eq_inner`:
  `∫_{A\G} conj((E ψ₂)(q̇)) (E ψ₁)(q̇) dν(q) = (ψ₂, ψ₁)` for the product of V.2.
- `rationalOrbitSectionInner_apply`: the defining formula.
- `notMem_discreteSeriesOrbit_of_mem`: if `omega' ∉ O`, no element of the orbit `O'` of `omega'`
  lies in `O`.
- `integral_conj_rationalOrbitWavePacket_mul_eq_zero`: if `omega' ∉ O`,
  `∫_G conj(f_{ψ'}(g)) f_ψ(g) dμG(g) = 0`.
- `integral_conj_rationalOrbitWavePacket_mul`: for `ψ'`, `ψ` over `O`,
  `∫_G conj(f_{ψ'}(g)) f_ψ(g) dμG(g) = μA(A_G ∩ G¹) rationalOrbitSectionInner … ψ' ψ`.

## Proof notes

1. Fubini: `conj(∫_Y e y x dμY) f x = ∫_Y conj(e y x) f x dμY` (`integral_conj`,
   `integral_mul_const`), then `integral_integral_swap` with `hint`.
2. Independence: `c = b.rescale a` for some `a > 0` (`exists_pos_rescale_eq`), and
   `coefficientTensorInvariantForm_rescale`. `discreteSeriesCoefficientForm_eq` unfolds the
   definition and applies this to the chosen form and `b`; `_inner` is
   `InvariantPositiveForm.rescale_inner`.
3. `integral_conj_mul_out_self_eq_inner`: choose `b` by `isUnitarizable_of_isSquareIntegrable`,
   rewrite with `discreteSeriesCoefficientForm_inner` and apply `integral_conj_mul_out_self`.
4. Disjointness: the orbits are `MulAction.orbit`s; `MulAction.orbit_eq_iff` turns
   `ω ∈ O ∩ O'` into `O = O'`, contradicting `omega' ∉ O`.
5. Main theorems: `conj(f_{ψ'}(g)) f_ψ(g)` is rewritten by `rationalOrbitWavePacket_apply`; the
   orbit measure is finite (`isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure`),
   hence s-finite, and step 1 with `hint` gives `∫_{O'} (E^G_G ψ'_{ω'}, f_ψ)_G dω'`. For almost
   every `ω'` the integrand `g ↦ conj((E^G_G ψ'_{ω'})(g)) f_ψ(g)` is `μG`-integrable
   (`Integrable.prod_left_ae`), so the pairing theorems apply: off the orbit,
   `integral_conj_mul_rationalOrbitWavePacket_eq_zero` (with step 4) gives `0` almost
   everywhere; on the orbit, `integral_conj_mul_rationalOrbitWavePacket_of_mem` gives
   `μA(A_G ∩ G¹) d(ω)⁻¹ (ψ'_ω, ψ_ω)_b`, which is `μA(A_G ∩ G¹) (ψ'_ω, ψ_ω)` by
   `discreteSeriesCoefficientForm_inner`; the constant leaves the integral
   (`integral_const_mul`).

## Open obligations

- The hypothesis `hint` is the absolute convergence of the double integral, which Waldspurger
  takes from Lemma VI.2.2; that lemma is not proved here. The hypotheses `hcont` and `hintA`
  and the normalization of the measures are as in `RationalOrbitWavePacketPairing` (see the open
  obligations there).
- The normalization `mes(A_G ∩ K) = 1` and the relation between `A_G ∩ K` and `A_G ∩ G¹`.
- The same-orbit theorem uses the same base point `omega` for both sections; sections over `O`
  based at another point of `O` (and the comparison of the orbit measures for different base
  points) are not treated.
- Part (i) and the general case of part (ii) (`M`, `M'` arbitrary, with `W(M'|G|M)`, `µ(ω)`,
  `γ(G|M)`, `c(G|M)` and `⁰c_{P'|P}(s, ω)`, through Lemmas VII.1.2, VII.1.4 and Propositions
  VI.4.1 and VII.2.1) are not addressed.
