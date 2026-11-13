# Compact parabolic covers of actual adelic points

Author: Worker 2.

Let `F` be a number field, `G` a connected reductive group over `F`, and
`p : P ⟶ G` a parabolic subgroup. This module proves, with no further
hypotheses, that there is a compact set `Ω ⊆ G(𝔸_F)` with `P(𝔸_F) · Ω = G(𝔸_F)`.
When a split component of `G` factors through `p`, it also proves that `Ω` can
be chosen inside the norm-one subgroup `G(𝔸_F)¹`. In particular, both hold for
the canonical minimal standard parabolic of every actual Siegel setup.

The compact factor is a **set**, not a subgroup, and maximality is not
claimed. This is the unconditional replacement for parabolic Iwasawa existence
(`AdelicGroupPoints.ParabolicIwasawaStatement`) in arguments that only use
compactness of the factor and the covering equality. The finite-place Iwasawa
input `FinitePlaceGroupPoints.ParabolicIwasawaStatement` is not used.

## Definitions

- `AdelicGroupPoints.HasCompactParabolicCover F G P p` holds when some
  `Ω : Set (AdelicGroupPoints F G)` is compact and
  `Set.range (map F P G p) * Ω = Set.univ`. The image of the actual adelic map
  of `p` is on the left and the compact set on the right. This is the same
  order as in `IsParabolicIwasawaCompact`.
- `AdelicGroupPoints.HasCompactNormOneParabolicCover F G P p` adds the
  condition `Ω ⊆ normOneSubgroup F G`, the existing norm-one subgroup.

Topologies are the existing regular-function evaluation topologies on actual
scheme points over the adeles and over each completion.

## Results

Generic lemmas:

- `CoordinateCompactAssembly.exists_isCompact_range_mul_eq_univ` is the set
  version of the published `range_mul_coordinateSubgroup_eq_univ`. Suppose
  compact local sets `Ω i` lie inside subgroups `K i` that have a continuous
  product lift (`CompactProductLift`), and coordinates separate points.
  Suppose also that every global point lies in `Ω i` at almost every `i`, that
  finitely supported source families lift, and that `range (φ i) * Ω i = univ`
  at every `i`. Then a compact global set `Ω'` exists whose points have all
  coordinates in the `Ω i`, and `range f * Ω' = univ`. The set `Ω'` is the image
  under the lift of the Tychonoff-compact product of the `Ω i`.
- `QuotientIntegration.compactSpace_leftQuotient_of_surjective`: let
  `e : H →* H'` be a continuous surjective homomorphism with `Γ.map e ≤ Γ'`.
  Then compactness of `Γ \ H` implies compactness of `Γ' \ H'`. Here
  `Γ \ H` is `Induction.LeftQuotient`, whose classes are the cosets `Γ g`.
- `QuotientIntegration.exists_isCompact_mul_eq_univ`: in a locally compact
  topological group `H`, a subgroup `Γ` with compact `Γ \ H` has a compact set
  `Ω` with `Γ * Ω = univ`.

Local and global results:

- `FinitePlaceGroupPoints.exists_isCompact_parabolic_cover`: at every finite
  place `v`, a compact `Ω_v ⊆ G(F_v)` satisfies `P(F_v) · Ω_v = G(F_v)`. Here
  `P(F_v)` is the image of `P.affinePointsTarget p` at the completion.
- `AdelicGroupPoints.hasCompactParabolicCover_of_local_integral`: let `G` and
  `P` have affine underlying schemes. Suppose there are local compact covers at
  every place and a family satisfying
  `IntegralIwasawaFamily.IsIntegralIwasawaFamily`. Then
  `HasCompactParabolicCover` holds. Connected reductivity is not needed for this
  step.
- `AdelicGroupPoints.hasCompactParabolicCover`: unconditional for every
  connected reductive `G` and every `IsParabolicSubgroup p`.
- `AdelicGroupPoints.HasCompactParabolicCover.exists_mul_range_eq_univ`: the
  inverse set gives the opposite order, `Ω⁻¹ · P(𝔸) = G(𝔸)`.
- `AdelicGroupPoints.hasCompactNormOneParabolicCover_of_splitComponent`: let
  `G` be connected reductive with affine structure morphism and `p` parabolic.
  If `a : Z ⟶ P` is such that `a ≫ p` is a split component
  (`IsSplitComponent`), then `HasCompactNormOneParabolicCover F G P p` holds.
- `AdelicSiegelFactors.IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover`:
  for an actual Siegel setup `IsSiegelAlgebraicSetup F G T i ν T₀ j` with
  connected reductive `G`, the canonical minimal standard parabolic
  `Standard.parabolicHom i ν ∅` has a compact norm-one cover.

## Proofs

**Finite places.** Base change `G` and `p` to the completion `F_v`.
`baseChanged_isConnectedReductive` and `baseChange_isParabolicSubgroup` keep
connected reductivity and parabolicity. The completion is a nonarchimedean
local field (`FiniteCompletion.isNonarchimedeanLocalField`). The published
`compactSpace_leftQuotient_pointImage_of_dynamic`, applied to the proved
`parabolicDynamic` and `BruhatTits.dynamicParabolicQuotientCompact`, gives
compactness of the quotient of rational points of the base change by the image
of `P`. The continuous group isomorphism `baseChangeContinuousMulEquiv` sends
that image into the image of `P(F_v)`, by `baseChangeMulEquiv_map`. So the
quotient `P(F_v) \ G(F_v)` of the actual completion points is compact. The
local points are a locally compact topological group
(`PlaceGroupPoints.locallyCompactSpace`). The generic lemma then gives `Ω_v`.

The covering argument is the standard one. Choose a compact neighbourhood `C`
of `1`. The open sets `π(g · interior C)` cover the compact quotient, so
finitely many do. The union of the corresponding translates `g · C` is
compact, and its product with `Γ` is everything.

**Assembly.** Take the integral family `K` from the proved
`IntegralIwasawaFamily.existenceStatement`, extended by the full group at the
archimedean places (`extendFinite`). Call a place *good* if `K` there is
compact and covers. This holds at almost every place, and the local compact
sets are patched at the remaining places with `patchFamily`. At archimedean
places the local set is the compact subgroup from the proved
`InfinitePlaceGroupPoints.parabolicIwasawaStatement`. At finite places it is
`Ω_v` from above.

To lift, use the subgroup family that equals `K` at good places and the whole
group elsewhere. It agrees with `K` almost everywhere, so the published
`IsUniformlyIntegral.of_eventuallyEq` and `compactProductLift` give a
continuous lift of its full product. Every local set lies in this family. The
set-version assembly then applies with the published adapters `ext_atPlace`,
`atPlace_map`, `eventually_atPlace_mem_of_finite` and
`exists_atPlace_eq_of_eventually_one`.

**Norm-one refinement.** The published
`PositiveRealTorus.splitComponentNormOneDecomposition`, with the proved
`centralSplitTorusCharacter`, gives a continuous multiplicative equivalence
`e : A_Z × G(𝔸)¹ ≃ₜ* G(𝔸)`. Here `A_Z` is the intrinsic positive subgroup of
the split component and the forward map is `(s, n) ↦ (a ≫ p)(s) · n`. Replace
`Ω` by the image of its norm-one coordinates under `e.symm`. This image is
compact and lies in `G(𝔸)¹`. If `g = p(y) · w` with `w ∈ Ω`, then
`w = p(a(s)) · n`, so `g = p(y · a(s)) · n` with `n` in the new set. For a
Siegel setup, the split component `z : Z₀ ⟶ T` followed by
`torusToStandardParabolic` gives the required factorization, by
`torusToStandardParabolic_comp`. Parabolicity comes from the minimal-parabolic
conjunct of the setup.

## Provenance and scope

This is derived infrastructure. Springer, *Reduction theory over global fields*
(1994), §2.1, printed p.211 (PDF p.5), works with exactly such a compact
**set**. He deduces compactness of `G(𝔸)/P(𝔸)` from `(G/P)(𝔸)` and concludes
that "there is a compact subset K of G(A)" with
`G(A)¹ = K·(S(A) ∩ G(A)¹)·P(A)¹`. His compact sets in §2.1–2.6 are not required
to be subgroups. His compact factor stands to the left of the parabolic; the
order used here is the opposite one, and
`HasCompactParabolicCover.exists_mul_range_eq_univ` converts between the two by
inversion. The registered source is `springer-1994-reduction-global-fields`,
SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.

The implemented route differs from Springer's. Instead of the adelic flag
variety, it uses compactness of `P(F_v) \ G(F_v)` at the finitely many bad
finite places: Renard, *Représentations des groupes réductifs p-adiques*
(2026), V.5.1 Corollary, printed p.123 / PDF p.129, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. At the remaining
places it uses the published integral and archimedean Iwasawa results.
Getz–Hahn (2024), §2.7, Theorem 2.7.1, printed p.71
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`) states the
subgroup version,
which this module does not prove.

No maximality, no subgroup property and no finite-place Iwasawa decomposition
is asserted. The norm-one theorem needs a split component factoring through
the given parabolic as an explicit hypothesis. For Siegel setups the setup
supplies it.
