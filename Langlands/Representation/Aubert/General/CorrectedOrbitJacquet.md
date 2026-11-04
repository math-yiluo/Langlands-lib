# The orbit Jacquet maps of the corrected Aubert complex

Module: `Langlands.Representation.Aubert.General.CorrectedOrbitJacquet`,
namespace `Langlands.Aubert.General.CorrectedFiltration`.

This pair is Part B of the conditional proof of
`CorrectedFiltration.CorrectedGradedTransitionTarget`
(task `d6be9c3b-ff6f-425c-9bb5-84c973b9568f`). It constructs the orbit
Jacquet maps `Θ` and proves the laws listed in the interface structure
`OrbitJacquetData` (CorrectedGradedInterface). The entry declarations are the
definition `orbitJacquetData` and the theorem `nonempty_orbitJacquetData`.
Both take as explicit hypotheses the structural facts about the double coset
that the Library does not have; see "Hypotheses" below. The map itself is the
definition `orbitJacquetMap`. Its laws are the theorems `orbitJacquetMap_*`,
which hold for individual subgroups and do not need the indexed families.

Author: Worker 1255. The interface `OrbitJacquetData` that this pair
instantiates is by Worker 969 (CorrectedGradedInterface).

## Provenance

This is an internal derived construction. It is not transcribed from the
literature. The Markdown of `CorrectedFiltrationStatements` quotes the source
of the construction: the isomorphism
`f ↦ (l ↦ ∫_{U_I ∩ w⁻¹ P_J w \ U_I} f(w u l) dµ(u))` of the erratum
(A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), p. 4689), redone by Ban and
Jantzen (Glasnik Matematički 51 (2016), (4.1) on p. 160). Here `Θ` is that
formula in the Library's conventions, with functions restricted to `P_I`.
`Θ φ` corresponds to the value of the formula at `l = 1`, and the
`M_I`-equivariance law accounts for the other values. No page of either source was re-read for
this pair; the conventions below are those of the Library and of the
interface.

The construction specializes the generic split-kernel value integral
`Induction.splitKernelValueIntegral` (SplitKernelValueIntegral, same
candidate) to the Levi projection of `P_I`. The published inputs are:

- `IsSemidirectDecomposition` with `projection`, `projection_levi`,
  `projection_eq_one_iff`, `projection_inv_mul_mem`, `levi_le`,
  `unipotent_le`, `le_normalizer` and `levi_le_normalizer`;
- `Geometric.orbitPiece`, `Geometric.orbitStabilizer` and
  `Geometric.stabilizerToInducing` (`q ↦ m⁻¹ q m`);
- `Jacquet.Localization.smoothObject`, `action`, `mk`, `mk_apply_subgroup`,
  `lift`, `relations`, `sub_mem_relations`, `transitionLinear` and its laws
  `transitionLinear_comp`, `transitionLinear_surjective`,
  `transitionLinear_natural`, and `mapLinear`;
- `HaarModulus.normalizerConj`, `closedNormalizerCharacter`,
  `closedRestrictCharacter`, `closedInverseHalfCharacter`,
  `Jacquet.inverseHalfCharacter_apply`, `conjugationEquiv`,
  `conjugationFunctor` and `jacquetFunctor`;
- `compactOpenSubgroupBasis` (Topology/CompactOpen/NeighborhoodBasis),
  `Haar.compactOpenCoverUnimodularity` and
  `QuotientIntegration.compatibleMeasureExists`;
- `Jacquet.Localization.IsLimitOfCompactSubgroups`
  (LocalizationExactnessStatement);
- Mathlib's `mulEquivHaarChar_trans_symm`, `NNReal.sqrt` and
  `Subgroup.isOpen_mono`.

## Conventions

These follow the interface. `m` is a lift of `w⁻¹`. The orbit piece is
`c-Ind_{P_I ∩ m P_J m⁻¹}^{P_I}` of the coefficient `q · [v] = [(m⁻¹ q m) v]` on
the actual coinvariants `E_{U_J}`. `K` satisfies `x ∈ M_I ↔ m⁻¹ x m ∈ M_K`.
For a surviving `J = S \ s` (`K ⊆ J`, `w` minimal in `W_J w W_I`), the
monotonicity of `P` and the antitonicity of `U` give `U_J ≤ U_K ≤ P_K ≤ P_J`
and `m⁻¹ M_I m = M_K ≤ P_J`.

## The map

For subgroups `P_I = M_I ⋉ U_I` (`hdI : IsSemidirectDecomposition PI MI UI`),
`P_J` normalizing `U_J`, `U_J ≤ U_K ≤ P_J`, and `m ∈ G`:

- `orbitKernelIntersection hdI UK m` is the subgroup
  `{n ∈ ker(P_I → M_I) : m⁻¹ n m ∈ U_K}` of the kernel of the actual Levi
  projection (`mem_orbitKernelIntersection`). It does not depend on `J`, so all
  surviving `J` integrate over the same quotient with the same measure.
- `orbitUnipotentIntersection UI UK m = U_I ∩ m U_K m⁻¹` in `G`
  (`mem_orbitUnipotentIntersection`).
- `orbitInducing hPJ E` is `E_{U_J}` with the action `p · [v] = [p v]` of `P_J`.
  For `P_J = P (S \ s)` and `hPJ = (h J).le_normalizer` it is the interface's
  `inducingObject`. `orbitCoefficient PI hPJ m E` is its composite with the
  stabilizer map, and `orbitCoefficient_isSmooth` proves it smooth.
- `orbitTransition hUJK E : E_{U_J} → E_{U_K}` is
  `Jacquet.Localization.transitionLinear UJ UK hUJK 1 1`, `[v] ↦ [v]`.
- `orbitKernelIntersection_iff`: under `(S1)` and `U_K ≤ P_J`, an element of
  the kernel lies in `orbitKernelIntersection` if and only if it lies in the
  orbit stabilizer `P_I ∩ m P_J m⁻¹`. This is the `hI` hypothesis of the
  generic value integral.
- `orbitTransition_invariant`: under `(S1)` the transition kills the action
  of `U_I ∩ m P_J m⁻¹`, because `m⁻¹ x m ∈ U_K` acts trivially on `E_{U_K}`
  (`mk_apply_subgroup`).
- `orbitLevi_mem`: if `m⁻¹ M_I m ≤ P_J`, then `M_I` lies in the stabilizer.
- `orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν` is the linear map

  ```text
  Θ φ = ∫_{(U_I ∩ m U_K m⁻¹) \ U_I} [φ(n)]_{U_K} dν(n)
  ```

  from the orbit piece to `E_{U_K}`. It is `splitKernelValueIntegral` for the
  retraction `r = hdI.projection` (assumed continuous, `hr`), the section
  `Subgroup.inclusion hdI.levi_le`, `H = P_I ∩ m P_J m⁻¹`,
  `I = orbitKernelIntersection hdI UK m`, the coefficient above and
  `T = orbitTransition`. `ν` is any measure on the quotient that is finite on
  compact sets.

## Laws of the map

- `orbitJacquetMap_unipotent`: if right translations by the kernel preserve
  `ν`, then `Θ (u · φ) = Θ φ` for `u ∈ U_I`
  (`splitKernelValueIntegral_translate`).
- `orbitJacquetMap_transition`: for a second parabolic `P_{J'}` normalizing
  `U_{J'}` with `U_J ≤ U_{J'} ≤ U_K ≤ P_{J'}`, `(S1)` and `m⁻¹ M_I m ≤ P_{J'}`:
  if `ψ(q)` is the transition `E_{U_J} → E_{U_{J'}}` of `φ(q)` for every
  `q ∈ P_I`, then `Θ' ψ = Θ φ`. The integration subgroup and `ν` are the same
  for both, so this is `splitKernelValueIntegral_eq_of_eval` with
  `transitionLinear_comp`.
- `orbitJacquetMap_natural`: for a morphism `f : E ⟶ E'`, if `φ'(q)` is the
  image of `φ(q)` under `E_{U_J}(f)` for every `q`, then
  `Θ φ' = E_{U_K}(f) (Θ φ)` (`splitKernelValueIntegral_map_of_eval` with
  `transitionLinear_natural`). This law is not an interface field.

The remaining laws assume that `G` is Hausdorff, that `P_I`, `U_I` and `P_J`
are closed, and that `ν` is compatible (`IsCompatible`) with regular,
right-invariant Haar measures `μN` on the kernel and `μI` on the kernel
intersection. The levi law needs right invariance only for `μI`.

- `projection_ker_compactOpenBasis`: compact open subgroups form a
  neighborhood basis of `1` in the kernel. The kernel is nonarchimedean
  (`nonarchimedeanGroup_of_isInducing`) and locally compact (closed in the
  closed subgroup `P_I`, `isClosed_projection_ker`), so
  `compactOpenSubgroupBasis` applies.
- `orbitJacquetMap_surjective`: `Θ` is surjective
  (`splitKernelValueIntegral_surjective` and `transitionLinear_surjective`).
- `orbitTransition_descent_injective`: let `P_J = M_J ⋉ U_J` (`hdJ`), and
  assume `(S1)` and `(S2)`. Then the transition, descended to the coinvariants
  of `U_I ∩ m P_J m⁻¹` (`Induction.splitKernelValueDescent`), is injective. Its
  left inverse is `[v]_{U_K} ↦ [[v]_{U_J}]`, defined by
  `Jacquet.Localization.lift`. To see that this is well defined, write
  `u ∈ U_K` as `u = a · (a⁻¹ u)` with `a` the `M_J`-component of `u` and
  `a⁻¹ u ∈ U_J`. Then `a ∈ M_J ∩ U_K`, so `m a m⁻¹ ∈ U_I` by `(S2)`. Also
  `m a m⁻¹` lies in the stabilizer and acts on `E_{U_J}` as `a`. Hence
  `[[u v]_{U_J}] = [[a v]_{U_J}] = [[v]_{U_J}]`.
- `orbitJacquetMap_ker_le`: under `(S2)`, `Θ φ = 0` implies that `φ` lies in
  the actual relations `Jacquet.Localization.relations … ((U I).subgroupOf
  (P I)) 1` of the orbit piece. `splitKernelValueIntegral_mem_ker` with the
  injectivity above puts `φ` in the span of the `n · φ - φ` for `n` in the
  kernel. Each generator lies in the relations by `sub_mem_relations`.
- `orbitJacquetMap_levi`: let `P_K = M_K ⋉ U_K` (`hdK`) with `U_K` closed, let
  `hK : x ∈ M_I ↔ m⁻¹ x m ∈ M_K`, and assume the modulus identity `(D07)`.
  Then for `l ∈ M_I`

  ```text
  δ_{U_I}^{-1/2}(l) · Θ (l · φ) = l · Θ φ   in Ad(m)(r_K E),
  ```

  with the action `l · [v] = δ_{U_K}^{-1/2}(m⁻¹ l m) [(m⁻¹ l m) v]` of
  `(conjugationFunctor m hK).obj ((jacquetFunctor hdK hUKc).obj E)`. The
  section law `splitKernelValueIntegral_section` gives
  `Θ (l · φ) = c(l) • τ l (Θ φ)`, where `τ l [v] = [(m⁻¹ l m) v]` and
  `c(l) = splitKernelValueRatio`. The ratio is computed by
  `mulEquivHaarChar_eq_closedNormalizerCharacter`: if a topological
  isomorphism `e : X ≃ₜ* Z` onto a closed subgroup carries `φ` to conjugation
  by `g`, then `mulEquivHaarChar φ` is the normalizer character of `Z` at `g`.
  It is applied through `projectionKerEquiv` (kernel `≃ₜ* U_I`) and
  `orbitKernelIntersectionEquiv` (kernel intersection
  `≃ₜ* U_I ∩ m U_K m⁻¹`). This gives
  `c(l) = δ_Z(l)⁻¹ / δ_{U_I}(l)⁻¹` with `Z = U_I ∩ m U_K m⁻¹`. The scalar lemma
  `inv_sqrt_mul_ratio_eq` (`a b = c²` gives
  `a^{-1/2} (c⁻¹ / a⁻¹) = b^{-1/2}`) then turns `(D07)` into
  `δ_{U_I}^{-1/2}(l) c(l) = δ_{U_K}^{-1/2}(m⁻¹ l m)`.

`levi_le_normalizer_orbitUnipotentIntersection` shows that `M_I` normalizes
`Z`, so `δ_Z` is defined on `M_I`. `isClosed_orbitUnipotentIntersection`,
`isClosed_orbitStabilizer`, `isClosed_orbitKernelIntersection`,
`continuous_stabilizerToInducing` and `continuous_levi_inclusion` are the
closedness and continuity facts used above.

## Hypotheses

The indexed form uses the interface's families `P M U`, `h`, `hclosed`,
`hU : Antitone U`, together with `[T2Space G]`, `hP : Monotone P` and
`hPc : ∀ J, IsClosed (P J : Set G)`. For fixed `I E w m K hK` it assumes:

- `(S1)` `hS1`: for every surviving `s` and every `x ∈ U_I`,
  `m⁻¹ x m ∈ P_J → m⁻¹ x m ∈ U_K`. Equivalently
  `U_I ∩ m P_J m⁻¹ = U_I ∩ m U_K m⁻¹`.
- `(S2)` `hS2`: for every surviving `s` and every `x ∈ M_J ∩ U_K`,
  `m x m⁻¹ ∈ U_I`.
- `hr`: the Levi projection `(h I).projection : P_I →* M_I` is continuous.
- `(D07)` `hD07`: for every `l ∈ M_I`,

  ```text
  δ_{U_I}(l) · δ_{U_K}(m⁻¹ l m) = δ_{U_I ∩ m U_K m⁻¹}(l) ^ 2,
  ```

  with the moduli `HaarModulus.closedRestrictCharacter`.
- For `nonempty_orbitJacquetData` only, `hcover`: every element of `U_I` lies
  in a compact open subgroup of `U_I`. The variant
  `nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups` assumes instead
  that `U_I`, as a subgroup of `P_I`, is a limit of compact subgroups.

For the rational points of a connected reductive group with its standard
parabolics, `(S1)` and `(S2)` are expected to follow from the root-system
descriptions of these intersections for `w` minimal in `W_J w W_I`, `(D07)`
from the corresponding identity of sums of roots, and `hr` and `hcover` from
standard topological facts. This pair proves none of that, and the Library
does not contain these facts, so they are premises here.

## The data

- `orbitJacquetData h hclosed hU hP hPc T cs I E w m K hK hS1 hS2 hr hD07 μN μI
  ν hCompatible : OrbitJacquetData P M U h hclosed hU T cs I E w m K hK` takes
  Borel structures on the kernel, the kernel intersection and the quotient,
  regular right-invariant Haar measures `μN` and `μI`, and a compatible
  quotient measure `ν` that is finite on compact sets. For surviving `s`, its
  `Θ s` is `orbitJacquetMap` with `P_J = P (S \ s)`, `U_J = U (S \ s)`,
  `hUJK = hU hKs`, `U_K ≤ P_J` from `(h K).unipotent_le` and `hP hKs`, and
  `m⁻¹ M_I m ≤ P_J` from `hK`, `(h K).levi_le` and `hP hKs`. The six fields are
  the six laws above. `unipotent_invariant` uses the right invariance
  `hCompatible.right_invariant`. `transition` uses
  `hU (Finset.sdiff_subset_sdiff_right Finset.univ hst)` for
  `U_J ≤ U_{J'}`.
- `nonempty_orbitJacquetData … hS1 hS2 hr hD07 hcover` proves that the data
  exist. It uses the Borel structures, the locally compact kernel and kernel
  intersection, and the Haar measures `haar`. `hcover` is transported to the
  kernel through `projectionKerEquiv`. The kernel is then covered by compact
  open subgroups, and `Haar.compactOpenCoverUnimodularity` makes both Haar
  measures right invariant. `compatibleMeasureExists` supplies `ν`, and its
  regularity gives finiteness on compact sets.
- `nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups … hS1 hS2 hr hD07
  hNc` is the same conclusion with `hcover` replaced by
  `hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I))`
  (every compact subset of `U_I`, as a subgroup of `P_I`, lies in a compact
  subgroup). The generic lemma
  `exists_compactOpen_mem_of_isLimitOfCompactSubgroups` derives `hcover` from
  it. In a nonarchimedean, weakly locally compact subgroup `V`, take a compact
  open subgroup `C₀` (`compactOpenSubgroupBasis`). Then `C₀ ∪ {v}` is compact,
  so it lies in a compact subgroup, and that subgroup is open because it
  contains `C₀` (`Subgroup.isOpen_mono`). Here `V` is nonarchimedean through
  `nonarchimedeanGroup_of_isInducing` and locally compact because it is closed
  in the closed subgroup `P_I`. The result is transported to `U_I` through
  `subgroupOfEquiv : (U I).subgroupOf (P I) ≃ₜ* U I`.

## Status

Compiles with `lean_check` together with CorrectedGradedInterface and
SplitKernelValueIntegral (no errors or warnings).
