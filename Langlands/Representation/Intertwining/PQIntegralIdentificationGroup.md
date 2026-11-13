# The integral over `V = N̄ ∩ U` on an abstract parabolic

Author: Worker 48. Module `Langlands.Representation.Intertwining.PQIntegralIdentificationGroup`,
namespace `Langlands.Aubert.General.IntegralIdentification`.

This helper module proves the group-level ingredients of Renard VII.3.4 (first paragraph of the
proof, printed pp.235–236 / PDF pp.241–242 of *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`). Everything is stated for abstract
topological groups. The concrete module
`Langlands.Representation.Intertwining.PQIntegralIntertwiningOperatorProof` applies it to rational
points of group schemes. These are internal lemmas. Renard uses the facts below without proof or
states them only in passing.

## Setting

In the section `Induced`: `G` is a locally compact nonarchimedean group, `P, M, N` are subgroups
with `hP : IsSemidirectDecomposition P M N` (so `P = M ⋉ N`), `N` is closed, and `σ` is a smooth
representation of `M`. `Ind` denotes `Induction.SmoothFunctions P (inducingRepresentation hP hN σ)`,
the space of normalized induction `i_P^G(σ)`. `ρI` is the right translation action and `ev` is
evaluation. Several theorems also assume `T2Space G` and `SecondCountableTopology G` (or
`SigmaCompactSpace G`).

## Unimodularity and limits of compact subgroups

- `isMulRightInvariant_of_forall_mem_compactOpen`: in a locally compact group where every
  element lies in a compact open subgroup, every regular Haar measure is right invariant. The
  modular character is trivial on compact open subgroups
  (`Induction.modularCharacter_eq_one_of_isCompact`).
- `exists_compactOpen_of_isLimit`: in a closed subgroup that is a limit of compact subgroups
  (`Jacquet.Localization.IsLimitOfCompactSubgroups`), every element lies in a compact open
  subgroup.
- `isLimitOfCompactSubgroups_of_le`: a closed subgroup of a limit of compact subgroups is again
  one.

## Descent through Jacquet relations

`eq_zero_of_mem_relations`: let `ρ` be a smooth representation of `G` on `X`, `U` a limit of
compact subgroups, `S ⊆ X` a `U`-stable subspace, and `T : S → W` a `U`-invariant linear map.
Then `T` vanishes on every `s ∈ S` lying in the Jacquet relations `relations ρ U 1`. Such an `s` is
a relation for one compact open subgroup `K` of `U`
(`Jacquet.Localization.mem_relations_iff_compact`). Exactness of the Jacquet functor of `K`
(`Jacquet.Localization.map_injective_of_smooth`, applied to the inclusion `S ↪ X`) shows that `s`
is a relation inside `S`. The relations inside `S` are killed by `T`.

## Conjugation by the Levi

For a subgroup `V` with `m⁻¹ V m ⊆ V` for all `m ∈ M` (hypothesis `hMV`):

- `conj_inv_mem`, `leviConj hMV m : V ≃ₜ* V`: conjugation `x ↦ m⁻¹ x m`.
- `leviConjFactor haar hMV m`: the scalar `haarScalarFactor (haar.map (leviConj hMV m)) haar`.
- `leviFactor hP hN haar hMV m = δ_P^{1/2}(m) · leviConjFactor haar hMV m`, where `δ_P^{1/2}` is
  `HaarModulus.closedHalfCharacter N hN M _`. It does not depend on `σ`.

## Evaluation lemmas

`eval_smoothInduced`, `eval_add`, `eval_smul`, `eval_zero`, `eval_mul_left` (the covariance
`f(p x) = δ_P^{1/2}(p) σ(p) f(x)`), `eval_unipotent_mul` (`f(n x) = f(x)` for `n ∈ N` when `N` is
unimodular, `IsUnimodularModulus`), `eval_levi_mul` (`f(m x) = δ_P^{1/2}(m) σ(m) f(x)`),
`exists_openSubgroup_eval_mul` (smoothness), and `isLocallyConstant_restrict` (the restriction of
`f` to any subgroup is locally constant).

## The integral (section `Integral`)

For a subgroup `V` with a measure `haar`:

- `integralOn hP hN σ V haar f = dualIntegral haar (fun v => f(v))`: Renard's `∫_V f(v) dv`, read
  against linear forms.
- `HasCompactSupportOn hP hN σ V f`: `f` vanishes on `V` outside a compact subset of `V`.
- `hasDualIntegral_integralOn`: if `haar` is finite on compacts and `f` has compact support on
  `V`, then `integralOn f` is a dual integral of `v ↦ f(v)`: for every linear form `ℓ`,
  `ℓ ∘ f|_V` is integrable and `ℓ(integralOn f) = ∫_V ℓ(f(v)) dv`. The restriction is locally
  constant, so `DualIntegral.exists_hasDualIntegral_of_isLocallyConstant` applies.
- `integralOn_add`, `integralOn_smul`, and `integralLinear`: linearity on a subspace of compactly
  supported functions.

### Right invariance under `U`

`integral_eval_mul_right`. Hypotheses: `N` is a limit of compact subgroups, `U` and `V` are
closed, `V ≤ U`, `U` is a limit of compact subgroups, and
`m : (N.subgroupOf U) × (V.subgroupOf U) ≃ₜ U` is a homeomorphism with `m (a, b) = a b`.
`haar` is a Haar measure on `V`. Conclusion: for every `f ∈ Ind`, every linear form `ℓ` and every
`u ∈ U`, `v ↦ ℓ(f(v u))` is integrable on `V` exactly when `v ↦ ℓ(f(v))` is, and the integrals
agree. Proof: in the group `U`, the function `y ↦ ℓ(f(y))` is left invariant under `N ∩ U`
(`eval_unipotent_mul`). `U` and `N ∩ U` are unimodular because they are limits of compact
subgroups. So `QuotientIntegration.compatibleMeasureExists` gives a nonzero regular
right-invariant measure on `(N ∩ U) \ U`. The Haar measure of `V` moved to `V ∩ U` inside `U` is
right invariant, and `QuotientIntegration.integral_mul_right_of_leftInvariant` applies.

`integralOn_smoothInduced`: hence `integralOn (ρI u f) = integralOn f` for `u ∈ U` when `f` has
compact support on `V`.

### Levi covariance

`integralOn_smoothInduced_levi`. Hypotheses: `V` is closed, `G` is Hausdorff and second
countable, `haar` is a Haar measure, `hMV` holds, and `f` has compact support on `V`. Then for
`m ∈ M`,
`integralOn (ρI m f) = leviFactor m • σ(m)(integralOn f)`.
Since `f(v m) = δ_P^{1/2}(m) σ(m) f(m⁻¹ v m)`, the change of variables `v ↦ m⁻¹ v m`
multiplies `haar` by `leviConjFactor m` (`isMulLeftInvariant_eq_smul`).

## Test functions (section `TestFunction`)

- `exists_open_coordinate`: let `G` be σ-compact, `P, V` closed, the orbit `P \ P V`
  (`Geometric.cosetOrbit P V 1`) locally closed, and `V ∩ P = 1`. Then for every neighbourhood
  `O` of `1` in `V` there is an open `O' ∋ 1` in `G` such that `p x ∈ O'` with `p ∈ P`, `x ∈ V`
  forces `x ∈ O`. This is the openness of the orbit map `V → P \ P V`
  (`Geometric.isOpenMap_cosetOrbitMap`, a Baire category argument).
- `exists_integralOn_eq`: hypotheses as in `exists_open_coordinate`, plus continuity of the Levi
  projection `hP.projection`, a Haar measure `haar` on `V`, and a set `D ∋ 1` that is locally
  closed and left `P`-invariant. Assume that every `f ∈ Ind` vanishing on `closure D \ D` has
  compact support on `V`. Then for every `v ∈ σ` there is `f ∈ Ind` vanishing on `closure D \ D`
  with `integralOn f = v`. Construction: choose a compact open subgroup `K` so small that
  `P ∩ K` fixes `v` under the inducing representation, `P K ∩ closure D ⊆ D`, and
  `x ∈ V ∩ P K` implies `x = p k` with `p` in a subgroup of `P` fixing `v`. The latter uses
  `exists_open_coordinate`. The section `compactDoubleCosetSection P _ K _ 1 v` of the Library is
  supported on `P K`. Its restriction to `V` is `v` times the indicator of the open set
  `V ∩ P K`. That set has positive measure and, by the compact-support hypothesis, finite measure.
  Dividing by the measure gives `f`.

In the application `D` is the double coset `P Q`, and the compact-support hypothesis is the
published theorem `pqBoundaryVanishingCompactSupport`.
