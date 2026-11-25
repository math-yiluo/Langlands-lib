# Proof: continuity of the action of `GL_{d+1}(F)` on Drinfeld's upper half space

`Langlands.Analytic.DrinfeldUpperHalfSpace.omegaActionContinuity` proves the
published statement `OmegaActionContinuityStatement.{u, v}` (module
`DrinfeldActionContinuityStatement`). For every nontrivially normed field `F`
with `ProperSpace F`, every nontrivially normed, ultrametric, complete field `K`
that is a normed `F`-algebra, and every `d` with `NeZero d`, the homomorphism
`(omegaAction F K d).ρAut : GL_{d+1}(F) →* Aut Ω` satisfies
`SaturatedAtlasPresentation.IsContinuousAction`: for every test triple `τ` of the
saturated presentation of `Ω`, the inverse image of Berkovich's set
`nearIdentity τ` is a neighbourhood of `1`. `GL_{d+1}(F)` carries Mathlib's
topology on units of the matrix algebra. The theorem uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof uses two supporting modules, ported with this file:
`DrinfeldMemberAction` (open stabilizers of the members `V_N` of the exhaustion
and norm-continuous actions on their chart algebras) and
`GeneralizedAffinoid/DomainNormSpectralTests` (spectral tests on arbitrary
represented domains from norm-continuous orbits).

## Notation

- `omegaSaturated F K d` is `ofSaturation (exhaustionPresentation F K d)`, the
  saturated presentation whose localization is `(omegaAction F K d).V`
  (`omegaAction_V`); it is definitionally the presentation of that object, so
  test triples of `Ω` are test triples of `omegaSaturated F K d`.
- `saturatedAction K γ` is `(compatibleHom K γ).saturationExtension`, whose image
  under the localization functor is `(omegaAction F K d).ρ γ`
  (`omegaAction_ρAut_hom`, by `rfl`).
- For a test triple `τ = (U, f, t)`, the chart `U` is an element of the
  local-domain family of the exhaustion atlas. `testRepresentative τ` is its
  chosen local domain: a member `testMember τ = V` of the exhaustion together
  with a represented domain `testDomain τ = D` of the chart algebra `O(V)`, and
  `testFunction τ = f` is a section of `D`. `testLocus_eq` identifies the locus of
  `τ` with the image of `D.locus` under the chart map of `V`.

## Step 1: the neighbourhood

By `continuous_memberAction`, the action `memberAction K V` of the open subgroup
`memberStabilizer K V` on `O(V)` has norm-continuous orbits. The supporting
theorem `domainSpectralSubgroup_mem_nhds_of_normContinuous` therefore makes
`W = {g | memberAction g ∈ domainSpectralSubgroup D f t}` a neighbourhood of `1`
in `memberStabilizer K V`. Since the stabilizer is open in `GL_{d+1}(F)`
(`isOpen_memberStabilizer`), the image of `W` in `GL_{d+1}(F)` is a neighbourhood
of `1` (`IsOpenEmbedding.map_nhds_eq`), and so is its inverse image under
inversion. For `γ` in the latter, `γ = g⁻¹` for some `g ∈ W`
(`omegaAction_preimage_nearIdentity_mem_nhds`).

## Step 2: membership gives the strong test relation

Let `g ∈ W` and `γ = g⁻¹`. Membership in the spectral test subgroup means that
`memberAction g` preserves `D.locus` and that every point `x` of the spectrum of
`D.algebra` satisfies `x(σ(f) − f) ≤ t` for the section operator
`σ = stabilizerSectionMap D (memberAction g)`. `strongNear_of_mem` proves
`StrongNear τ (saturatedAction K γ) (𝟙 _)`:

1. Inverse images. `memberAction g⁻¹ = (memberAction g)⁻¹` also preserves
   `D.locus`, and its spectrum action is the action of `γ`
   (`actionMap_exhaustionChartMap_smul`). Hence
   `preimage_image_eq_of_mem_locusStabilizer` gives
   `actionMap γ ⁻¹' τ.locus = τ.locus`: a point mapped into the locus lies in `V`
   because `γ` preserves `V`, so it is a chart point, and injectivity of the
   chart map of `V` and the stabilizer property move it back into `D.locus`. The
   identity has the same inverse image.
2. Covering by test pieces. The chart `U` itself is a test piece for both maps,
   since `γ` maps the locus into itself.
3. Bounds. For any test piece `i`, the restriction law of the strong map
   (`restriction_comm`, with `restriction_id`) writes the pullback of `f` along
   `γ` from `U` to `i` as the restriction to `i` of the pullback from `U` to `U`,
   and the identity's pullback is that restriction of `f`. The pullback from `U`
   to `U` equals `σ` (`saturatedAction_pullback_self`): both are bounded maps out
   of `D.algebra`, and by uniqueness in the representation property
   (`boundedHom_ext`) it suffices to compare them after composition with the
   structural map of `D`. On the saturation side,
   `localDomainPullback_comp_baseMap` and
   `localChartPullback_of_parent_admissible` reduce this composite to the
   original pullback of `compatibleHom K γ` from `V` to `V`, which is
   `selfPullback K V γ` (`compatibleHom_pullback_self`, from
   `ofChain_pullback_upper` and uniqueness of maps with the coordinates of `γ`).
   On the other side, `stabilizerSectionMap_comp_baseMap` gives the forward map
   of `memberAction g`, which is by definition `selfPullback K V g⁻¹`. Pulling a
   point `p` of the test piece back along the restriction then gives
   `p(pullback(f) − restriction(f)) ≤ t` from the spectral bound.

## Step 3: the near relation in the localized category

`isNear_of_mem` writes `(omegaAction F K d).ρ γ` and `𝟙` as right fractions
with the identity denominator (`localizationFunctor_map_eq_fraction`,
`localizedQuasiIso_inv_hom_id`), so the strong relation of Step 2 gives
`IsNear τ ((omegaAction F K d).ρAut γ).hom (𝟙 _)`, that is, `γ` lies in the
inverse image of `nearIdentity τ` (`mem_preimage_nearIdentity_of_mem`).
`omegaActionContinuity` applies this to every `F`, `K`, `d` and `τ`.

## Relation to the suggested route

The statement's Markdown suggests a three-step route: preservation of the
polydiscs and members for `γ` near `1`, preservation of rational domains with
small displacement of pulled-back functions, and reduction of general affinoid
domains to rational ones by the Gerritzen–Grauert theorem. The implemented proof
follows it in this form: the member estimate is
`eventually_exists_isActionPullback`; rational domains of `O(V)` are handled by
the Library's norm-continuity theory for rational charts
(`RationalNormSectionContinuity`, after norm continuity of the action on `O(V)`
is established); and general domains reduce to rational ones through the
published `finiteRationalCover`, with injectivity of domain spectrum maps from
`spectrumEmbedding`.

## Scope

The theorem is exactly the published statement. Combined with the Hausdorff
instance in `DrinfeldGroupAction`, it shows that `omegaAction F K d` satisfies
`gSpaceProperty`; that consequence is not restated here.
