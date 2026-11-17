# Central normalization of the rational wave-packet calculation

This unit supplies the central-mass comparison needed for Waldspurger VII.2.1
in the case `M = G`. It is an elementary consequence of published compactness
and norm-kernel results. Its module is
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWavePacketCentralNormalization`;
all declarations below are in `Langlands.HarishChandraSchwartz`.

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, JIMJ 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`. I.1 (printed pp. 240–241, PDF pp. 6–7)
fixes a special maximal compact subgroup `K` and normalizes subgroup Haar
measure by `mes(A ∩ K) = 1`. The `M = G` argument for VII.2.1 is on
printed p. 318 (PDF p. 84). The published
`coefficientFourierTransform_rationalOrbitWavePacket` retains the mass
`μA(A ∩ G¹)`.

## Declarations and proof route

- `compactCentralSubgroup_le_maximalCompact`: for an arbitrary topological
  group, a compact central subgroup `C` lies in every maximal compact
  subgroup `K`. Centrality makes `C` normal, so `K ⊔ C` has carrier
  `K * C`, which is compact. Maximality gives its inclusion in `K`.
- `rationalNormKernelPart_eq_inf_maximalCompact`: for any closed central
  subgroup `A` of actual rational points, `A ∩ G¹ = A ∩ K`. The first
  inclusion uses the preceding lemma and the published
  `isCompact_rationalNormKernelPart`. The reverse inclusion uses the
  published `compactSubgroup_le_rationalCommonNormKernel`.
- `RationalWavePacketCentralMassNormalizationStatement`: the exact
  Prop-valued mass-one assertion on the preimage of `G¹` in `A`.
- `rationalWavePacketCentralMassNormalization`: proves that assertion
  from `μA(A ∩ K) = 1`, using equality of the two preimage subsets of `A`.
- `RationalSourceNormalizedOrbitPacketFourierStatement`: the exact
  conditional Prop-valued source-normalized `M = G` Fourier formula.
  For every discrete-series class `omega'`, the Fourier transform is
  `rationalOrbitSectionExtension s hs mu omega ψ omega'`, which equals
  the section at `omega'` on the orbit and zero off the orbit.
- `rationalSourceNormalizedOrbitPacketFourier`: proves the preceding
  conditional assertion by applying the published
  `coefficientFourierTransform_rationalOrbitWavePacket` and replacing
  its central mass by one. The proof does not rederive the packet
  calculation or change the packet, formal degree, or check convention.

The first two lemmas and the mass adapter are derived constructions. The
Fourier theorem is a conditional adapter: its analytic assumptions are
listed next. The two named proposition definitions have proofs in this
unit under exactly their displayed hypotheses. They are not targets for
the still unproved general-Levi computations.

## Exact Fourier hypotheses

Write `A = (GroupScheme.rationalPoints.map s).range`. In addition to the
field and group scope below, the Fourier statement takes an affine
commutative group scheme `T`, a central morphism `s : T.toGrp ⟶ G`,
closedness of `A`, and the finite-index condition
`(RenardCartan.splitValuationImage s).FiniteIndex`. These are the same
central-image hypotheses as the imported theorem; no existence or
maximal-split-center identification is asserted here.

The statement retains measurable and Borel structures on `G(F)`, `A`,
the left quotient `A \ G(F)` and the normal quotient `G(F) / A`. It
installs normality from centrality. Its remaining hypotheses are:

- A Haar, inversion-invariant measure `mu` on `G(F) / A`, and
  a discrete-series class `omega` modulo `A` with unitary
  rational-norm-character orbit `O`.
- A maximal compact subgroup `K`, a measure `μA` on `A` that is
  `SFinite`, left invariant, right invariant and finite on compacts,
  and `μA(Subtype.val ⁻¹' K) = 1`.
- A measure `μG` on `G(F)` finite on compacts, left invariant,
  right invariant and inversion invariant; a measure `ν` on
  `A \ G(F)`; `IsCompatible A μG μA ν`; and
  `ν.map (normalLeftQuotientHomeomorph A) = mu`.
- A section `ψ` assigning to each `ω ∈ O` a `CoefficientTensor` of
  `Quotient.out ω`; continuity of `ω ↦ coefficientTensorMap _ (ψ ω) g`
  for every `g`; and `μA`-integrability of `a ↦ f_ψ(a * g)` for
  every `g`.
- Weights `Ξ σ`, `L2Weights μG Ξ σ`, inversion symmetry of both
  weights, and `f : Space Ξ σ` with the exact function equality
  `⇑f = rationalOrbitWavePacket s hs mu hindex omega ψ`.
- Every discrete-series class `omega'` modulo `A`, with
  `HasTemperedCoefficients Ξ σ` for its chosen representative.

The conclusion uses `coefficientFourierTransform` at that representative,
with admissibility supplied by
`isSquareIntegrableModCentralSubgroup_out` and the factor
`discreteSeriesFormalDegree ... omega'`. This is the existing
`d(omega') π(f̌)` convention. The packet is the published
`rationalOrbitWavePacket`; it already uses
`rationalNormalizedDiscreteSeriesOrbitMeasure`, with the I.1 character
measure scale and reciprocal unramified self-twist stabilizer factor.
The new proof does not rescale that orbit measure.

`μA(A ∩ K) = 1` is the central part of the source's I.1 Haar
convention. `μG` retains the imported theorem's compatibility and
invariance assumptions; this adapter does not additionally assume
`μG(K) = 1`.

## Declaration dependencies

| New declaration | Exact preceding declarations used | Role |
| --- | --- | --- |
| `compactCentralSubgroup_le_maximalCompact` | `Subgroup.normal_of_le_center`, `Subgroup.mul_normal`, `IsCompact.mul`, `Maximal` | Elementary topological-group proof |
| `rationalNormKernelPart_eq_inf_maximalCompact` | `rationalNormKernelPart`, `isCompact_rationalNormKernelPart`, `compactSubgroup_le_rationalCommonNormKernel`, preceding lemma | Actual rational-point intersection proof |
| `RationalWavePacketCentralMassNormalizationStatement` | `rationalCommonNormKernel` | Exact central mass assertion |
| `rationalWavePacketCentralMassNormalization` | Preceding intersection proof and mass assertion | Source normalization adapter |
| `RationalSourceNormalizedOrbitPacketFourierStatement` | `rationalOrbitWavePacket`, `rationalOrbitSectionExtension`, `coefficientFourierTransform`, `discreteSeriesFormalDegree`, `isSquareIntegrableModCentralSubgroup_out` | Exact conditional `M = G` formula |
| `rationalSourceNormalizedOrbitPacketFourier` | Preceding mass adapter, `coefficientFourierTransform_rationalOrbitWavePacket` | Conditional Fourier consequence |

## Scope

The rational-point declarations use arbitrary nonarchimedean local fields,
affine locally finite type group schemes, and the canonical rational-point
topology. Connected reductivity, closedness and centrality of `A`, maximal
compactness of `K`, and the mass-one convention are explicit hypotheses.
No characteristic, splitting, quasisplitness, or positive-rank assumption
is made. The Fourier statement has independent field and
representation-carrier universes `u` and `uV` and uses complex
`SmoothRep` coefficient tensors. Maximal compactness is used without openness; therefore the
compact, open, maximal condition of a special maximal compact subgroup
supplies more than is needed here.

The measure-level adapter needs only a measure on `A`, since equality of
subsets already proves equality of their measures. In applications the
published packet theorems retain their Haar and quotient-compatibility
assumptions. This unit does not construct a special maximal compact
subgroup or a normalized Haar measure, and does not prove the general-Levi
formula of VII.2.1. All Schwartz membership, regularity, integrability,
quotient compatibility and tempered-coefficient assumptions above remain
conditional inputs. No strict positivity of the Plancherel density,
irreducibility of tempered induction, or finite Fourier support assumption
is introduced.
