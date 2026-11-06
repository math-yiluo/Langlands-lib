# Proposition VII.1.3 with the lattice map of Laurent coordinates

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitLaurentSmoothness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitSmoothness` (accepted candidate
  d6417274, not yet in the Library when this module was written): `fourierOrbitSection_mem_smooth`
  and `fourierOrbitSmoothSectionLinear` (Proposition VII.1.3, first assertion, for a supplied
  lattice map `n`); through its imports `fourierOrbitSection` (`ψ_f[O, P]`), Worker 200's
  `productInducedSmoothOrbitSections` (`C^∞(O, P)`), `UnitaryOrbitRepresentative`,
  `unitaryTorusParameter` and `torusCharacter`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.LaurentExponent` (accepted candidate
  297d4b59, not yet in the Library when this module was written): `laurentExponent ν e he`,
  `torusCharacter_laurentExponent`, `laurentExponent_mul`, `laurentExponent_eq_zero_of_isCompact`
  and `measurable_laurentExponent`; through its imports Worker 200's
  `HasLaurentUnitaryCoordinates ν e`, `commonNormKernel ν` with `mem_commonNormKernel`, and
  `RankinSelberg.LastRowReduction.eq_one_of_isCompact` (a continuous homomorphism to `ℝ≥0ˣ` is
  trivial on a compact subgroup).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Proposition VII.1.3, printed p. 316 (PDF p. 82): "Pour tout `f ∈ C(G)`, la fonction
  `ψ_f[O, P]` appartient à `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]` est
  continue."
- I.1, printed pp. 239–240 (PDF pp. 5–6): the unramified characters `X(G)` and the unitary
  subgroup `Im X(G)`.

`fourierOrbitSection_mem_smooth_of_hasLaurent` is the first assertion of Proposition VII.1.3
(source content) in the Library's torus formulation; `fourierOrbitLaurentSmoothSectionLinear` is
the map `f ↦ ψ_f[O, P]` of the second sentence, as a linear map, without its continuity.
Waldspurger has no coordinates on `Im X(M)`. The torus coordinates `e`, the Laurent condition
`HasLaurentUnitaryCoordinates ν e` (Worker 200) and the lattice map `laurentExponent ν e he` are
part of the Library's formulation, and `isOpen_commonNormKernel_of_continuous` is derived. This
module removes from `FourierOrbitSmoothness` the hypotheses on the lattice map `n` that
`LaurentExponent` proves: it sets `n := laurentExponent ν e he`. The growth bound on `n`
remains a hypothesis.

## Scope and hypotheses

`isOpen_commonNormKernel_of_continuous`: `M` is a group with a topology,
`[IsTopologicalGroup M]` and `[Nonempty (CompactOpenSubgroup M)]`, `I` a type, `ν : I → (M →* ℝ≥0ˣ)` and
`hνc : ∀ i, Continuous (ν i)`.

Section variables (as in the orbit section of `FourierOrbitSmoothness`): instances on `G`:
`Group`, `TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup`,
`SecondCountableTopology`, `T2Space`, `MeasurableSpace`, `BorelSpace`,
`Nonempty (CompactOpenSubgroup G)`; subgroups `P`, `M`, `U` of `G` with
`[LocallyCompactSpace P]`; `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`,
`hP : IsClosed P`, `hm : Continuous h.projection`; an open subgroup `K` with `hK : IsCompact K`,
`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`; `hG : ∀ g, modularCharacter g = 1`;
`hδ : ∀ q : P, modularCharacter q = closedRestrictCharacter U hU P … q`; a type `I` and
`ν : I → (M →* ℝ≥0ˣ)`; `π : IrreducibleAdmissibleRep ℂ M`; `hcof : CompactOpenCofinal M`; a
normal subgroup `C` with `hC : C ≤ center M`, a measurable and Borel structure on `M/C` and a
Haar measure `μM` on `M/C` that is inversion invariant;
`hsq : ∀ A : UnitaryOrbitRepresentative ν π`, square integrability of `A` modulo `C` for `μM`;
a left and right invariant measure `μ` on `G`; weights `Ξ σ : G → ℝ` with
`hw : L2Weights μ Ξ σ`; `hT : ∀ A`, tempered coefficients (`HasTemperedCoefficients Ξ σ`) of the
normalized induction of `A`; `hΞ : ∀ g, Ξ g⁻¹ = Ξ g`, `hσ : ∀ g, σ g⁻¹ = σ g`.

`fourierOrbitSection_mem_smooth_of_hasLaurent` also takes:

- a finite type `J`, `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`,
  `hνc : ∀ i, Continuous (ν i)`, `hPK' : ∀ g, ∃ p : P, ∃ k : K, g = p k`;
- `hsqπ`: square integrability of `π` modulo `C` for `μM`;
- `[MeasurableInv G]`, `[μ.IsInvInvariant]`, `[SigmaFinite μ]`, `hμK : μ K = 1`,
  `hδU : IsUnimodularModulus U hU`, `[Nonempty (CompactOpenSubgroup M)]`;
- a measure `μL` on `M` that is left and right invariant, inversion invariant and s-finite, with
  `[MeasurableInv M]`; weights `ΞM σM : M → ℝ` with `hwM : L2Weights μL ΞM σM`;
  `hTπ : HasTemperedCoefficients ΞM σM π`; `hTM : ∀ A, HasTemperedCoefficients ΞM σM A`;
  `hΞM : ∀ m, ΞM m⁻¹ = ΞM m`, `hσM : ∀ m, σM m⁻¹ = σM m`;
- a measure `νU` on `U` that is left and right invariant and s-finite;
  `hD : ConstantTermData νU δ`, `hνU : IsConjModulus … νU δ` and
  `hE : ConstantTermEstimate νU δ Ξ σ ΞM σM` for `δ = closedRestrictCharacter U hU M …`;
  `ht : TranslationWeights Ξ σ`, `htM : TranslationWeights ΞM σM`;
- `hPKiw : ∀ m u, m u ∈ K ↔ m ∈ K ∧ u ∈ K`, `hMK : μL {m | m ∈ K} = 1`,
  `hUK : νU {u | u ∈ K} = 1`;
- `he : HasLaurentUnitaryCoordinates ν e`, a real `Cn` and
  `hnσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cn (1 + σM m)`;
- `f : Space Ξ σ` (`f ∈ C(G)`) and `hint : ∀ A ψ`, the absolute convergence of Lemma VII.1.2
  for every representative `A` (integrability of
  `(x, k) ↦ conj (CompactInduction.integrand … A K x ψ k) · f x` for `μ × measure K hK`).

`fourierOrbitLaurentSmoothSectionLinear` and `fourierOrbitLaurentSmoothSectionLinear_apply` take
the same hypotheses with `hint` required for every `f ∈ C(G)`; `_apply` also takes `f`.

Compared with `fourierOrbitSection_mem_smooth`, the hypotheses `n`, `hn`, `K₀`, `hK₀`, `hnm` and
`hne` are dropped and replaced by `he`; `hnσ` is stated for `laurentExponent ν e he`.

## Definitions

- `fourierOrbitLaurentSmoothSectionLinear … : Space Ξ σ →ₗ[ℂ] productInducedSmoothOrbitSections ν
  π e h hU K hP hK hνc hm hPK'` is `f ↦ ψ_f[O, P]`. It is `fourierOrbitSmoothSectionLinear` with
  `n := laurentExponent ν e he` and `K₀` an arbitrary compact open subgroup of `M`.

## Results

- `isOpen_commonNormKernel_of_continuous`: the common norm kernel `commonNormKernel ν` is open.
- `fourierOrbitSection_mem_smooth_of_hasLaurent` (**Proposition VII.1.3, first assertion**):
  `ψ_f[O, P] ∈ C^∞(O, P)`.
- `fourierOrbitLaurentSmoothSectionLinear_apply`: the underlying section of the image of `f` is
  `fourierOrbitSection … f` (by `rfl`).

## Proof notes

1. `isOpen_commonNormKernel_of_continuous`: a chosen compact open subgroup `K₀` of `M` lies in
   `commonNormKernel ν` by `eq_one_of_isCompact`, so the kernel is open by `Subgroup.isOpen_mono`.
2. The main theorem applies `fourierOrbitSection_mem_smooth` with `n := laurentExponent ν e he`:
   `hn` is `laurentExponent_mul`; `K₀` is `Classical.arbitrary (CompactOpenSubgroup M)` and `hK₀`
   is `laurentExponent_eq_zero_of_isCompact`; `hnm` is `measurable_laurentExponent` with the
   openness of step 1; `hne` is `torusCharacter_laurentExponent`, read in the reverse direction.
3. The linear map is `fourierOrbitSmoothSectionLinear` with the same arguments.
4. The theorem and the definition use `set_option maxHeartbeats 1000000`, as
   `fourierOrbitSection_mem_smooth` does.

## Relation to the Library

- `commonNormKernelTopology` (`Langlands.Representation.Plancherel.NormKernelTopologyProof`)
  proves the openness of `commonNormKernel ν` for weakly locally compact nonarchimedean groups and
  continuous `ν i`. `isOpen_commonNormKernel_of_continuous` uses instead the existence of a compact
  open subgroup, which `fourierOrbitSection_mem_smooth` already assumes for `M`; it needs neither
  `NonarchimedeanGroup M` nor local compactness of `M`.
- For the canonical rational coordinates of a connected reductive group,
  `laurentExponent_rationalCanonical` (`LaurentExponent`) identifies `laurentExponent` with
  `rationalValuationCoordinates`.

## Open obligations

- The growth bound `hnσ` for Waldspurger's `σ` on `M` (I.1) is a hypothesis.
- The continuity of `f ↦ ψ_f[O, P]` (second assertion of Proposition VII.1.3) is not addressed.
- As in `FourierOrbitSmoothness`: the absolute convergence `hint` (for `Ξ = xi` it is
  `integrable_coefficientPairingIntegrand` of `InducedCoefficientConvergence`), Proposition II.4.5
  (`hE`), Lemma II.1.5 (`hw`, `hwM`) and the tempered coefficients `hT`, `hTM`, `hTπ` are
  hypotheses.
