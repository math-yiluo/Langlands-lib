# The inverse limit of an ℓ-divisible system

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.ContinuousLimit` (`ConeSpace`, `proj`,
`act`, `continuous_action`), `Langlands.Cohomology.DivisibleSystem.ReductionLimit`
(`reductionCone`), `Langlands.Cohomology.DivisibleSystem.ReductionAdic`
(`powSMul_moduleCat_hom_apply`) and
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`mem_sections_of_map_succ`,
`concrete_surjective_π_app_of_surjective_map`). Through their imports it uses
the published `DivisibleSystem` with `projection`, `epi_projection`,
`isZero_obj_zero` and `DivisibleSystem.map`, together with `powSMul`,
`comp_powSMul`, `map_powSMul` and `shortComplex_exact_congr`
(`Langlands.Cohomology.DivisibleSystem`); `reductionTower`, `reductionπ`,
`reductionπIsCokernel` and `reductionπ_map`
(`Langlands.Cohomology.DivisibleSystem.Reduction`); `IsSmooth`
(`Langlands.Representation.Smooth.Definitions`); and
`harrisEtaleDivisibleSystem`, `harrisEtaleSectionsDivisibleSystem`,
`harrisEtaleSectionsSystem`, `harrisEtaleAdicCohomology` and
`harrisEtaleAdicCohomologyZeroDivisibleIso`
(`Langlands.Cohomology.DivisibleSystem.HarrisEtale`,
`Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology`,
`Langlands.Shimura.Coefficients.HarrisEtaleCoefficients`).

From Mathlib it uses `IsAdicComplete` with `isAdicComplete_iff`, `SModEq`,
`IsSMulRegular`, `Ideal.adicModuleTopology` with the filter bases
`RingFilterBasis.moduleFilterBasis` and `AddGroupFilterBasis.nhds_zero_hasBasis`,
`IsTopologicalAddGroup.ext`, `nhds_iInf`, `nhds_induced`, `nhds_discrete`,
`Filter.comap_pure`, `Filter.hasBasis_iInf_principal`,
`Filter.HasBasis.eq_of_same_basis`, `ShortComplex.moduleCat_exact_iff`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.Exact.gIsCokernel`,
`Functor.epi_of_epi_map`, `Functor.mono_of_mono_map`,
`ModuleCat.epi_iff_surjective`, `ModuleCat.mono_iff_injective`,
`IsColimit.coconePointUniqueUpToIso` with
`IsColimit.comp_coconePointUniqueUpToIso_hom`, `NatIso.ofComponents`,
`IsLimit.postcomposeHomEquiv`,
`IsLimit.ofIsoLimit`, `IsLimit.extendIso`, `Cone.ext`, `Cone.extend`,
`Types.isLimitEquivSections`, `Concrete.isLimit_ext`, `isLimitOfPreserves` and
`preservesSmallestLimits_of_preservesLimits`.

All declarations are in the namespace `Langlands.Cohomology.DivisibleSystem`.

## Conventions

`ℓ` and `m` are natural numbers and `R` is a commutative ring. `T` is an
`ℓ`-divisible system (the published structure `DivisibleSystem C ℓ` in an
abelian category `C`): objects `T m = T.obj m` forming the inverse system
`T.tower : ℕᵒᵖ ⥤ C`, transition maps `j = T.projection h : T k ⟶ T p` for
`p ≤ k`, and maps `i = T.inclusion h : T m' ⟶ T m` for `m' < m`, with
`ℓ ^ m = 0` on `T m`, the short exact sequences
`0 → T m' → T m → T (m - m') → 0`, `i` a kernel of `ℓ ^ m'` on `T m`, and
the flatness condition that `ℓ ^ a` and `ℓ ^ b` form an exact sequence on
`T (a + b)`. `powSMul ℓ m X : X ⟶ X` is the published "multiplication by
`ℓ ^ m`"; for modules its underlying map is `x ↦ ℓ ^ m • x`.

Throughout, `c : Cone T.tower` is a cone with vertex `c.pt` and projections
`c.π.app (op m) : c.pt ⟶ T m`, and `hc : IsLimit c` says that `c.pt` is the
inverse limit `L = lim_m T m`. Results are stated for every limit cone, not
only for the chosen limit `limit T.tower`, so that they apply to the
published `harrisEtaleAdicCohomology`, which is a limit of an isomorphic
system. For an `R`-module `N`, `(Ideal.span {ℓ}) ^ m • ⊤` is the submodule
`ℓ ^ m N`; `IsAdicComplete (Ideal.span {ℓ}) N` is Mathlib's statement that
`N` is Hausdorff and complete for the `ℓ`-adic topology; and
`IsSMulRegular N ℓ` says that `x ↦ ℓ • x` is injective on `N`, so `N` has no
`ℓ`-torsion. `reductionTower ℓ X` is the published inverse system of the
cokernels `X / ℓ ^ m X` of `powSMul ℓ m X`, with projections
`reductionπ ℓ X m : X ⟶ X / ℓ ^ m X`, and `reductionCone ℓ X` is the cone of
these projections with vertex `X`.

## Systems of modules

Here `T : DivisibleSystem (ModuleCat R) ℓ`, with module carriers in an
arbitrary universe.

- `mem_span_pow_smul_top_iff`: in any `R`-module, `x ∈ (ℓ) ^ m • ⊤` if and
  only if `x = ℓ ^ m • y` for some `y`.
- `pow_smul_obj_eq_zero`: `ℓ ^ m • x = 0` for `x ∈ T m`.
- `projection_surjective`: each `j : T k → T p` is surjective.
- `projection_projection_apply`: composing `j`'s elementwise.
- `projection_hom_apply_eq_zero_iff`: for `p ≤ k`, `j x = 0` in `T p` if and
  only if `ℓ ^ (k - p) • x = 0`. Proof: for `p = 0`, `T 0 = 0`; otherwise write
  `p = k - m'` with `m' < k` and use exactness of
  `0 → T m' → T k → T (k - m') → 0` and of `T m' → T k → T k` (second map
  `ℓ ^ m'`).
- `exists_pow_smul_eq_of_pow_smul_eq_zero`: in `T k` with `k = a + b`, an
  element killed by `ℓ ^ b` is of the form `ℓ ^ a • y` (flatness).
- `projection_π_apply`, `ext_of_isLimit`, `exists_π_apply_eq`: the projections
  from a cone commute with the `j`'s; two elements of the limit with the same
  projections are equal; a family `s n ∈ T n` with `j (s (n + 1)) = s n` for
  all `n` is the family of projections of some element of the limit (through
  `Types.isLimitEquivSections` and the published `mem_sections_of_map_succ`).
- `π_surjective`: every projection `L → T m` is surjective (published
  `concrete_surjective_π_app_of_surjective_map`).
- `π_hom_apply_eq_zero_iff` (main lemma): the projection of `x ∈ L` to `T m`
  is `0` if and only if `x = ℓ ^ m • y` for some `y ∈ L`. Proof of the
  forward direction: for each `n`, the projection of `x` to `T (n + m)` lies in
  the kernel of `j : T (n + m) → T m`, so it is killed by `ℓ ^ n` and hence is
  `ℓ ^ m • w n` by flatness; the images `s n ∈ T n` of the `w n` do not depend
  on the choice of `w n` (two choices differ by an element killed by `ℓ ^ m`,
  which maps to `0` in `T n`), so they are compatible, and the element `y` of
  the limit with projections `s n` satisfies `ℓ ^ m • y = x`.
- `π_hom_apply_eq_iff`: two elements of `L` have the same projection to `T m`
  if and only if they are congruent modulo `(ℓ) ^ m • L` (`SModEq`).
- `ker_π`: the kernel of the projection `L → T m` is `(ℓ) ^ m • L`.
- `isSMulRegular_of_isLimit`: `L` has no `ℓ`-torsion. If `ℓ • z = 0`, the
  projection of `z` to `T n` is the image under `j : T (n + 1) → T n` of an
  element killed by `ℓ`, hence `0`.
- `isAdicComplete_of_isLimit`: `L` is `ℓ`-adically complete and Hausdorff.
  Hausdorff: an element in every `(ℓ) ^ n • L` has all projections `0`.
  Complete: for a sequence `f` with `f m ≡ f n` modulo `(ℓ) ^ m • L` for
  `m ≤ n`, the projections of `f n` to `T n` are compatible, and the element
  of the limit with these projections is the limit of `f`.

## Abelian categories

Here `C` is any abelian category and `T : DivisibleSystem C ℓ`.

- `powSMul_comp_π c m`: `powSMul ℓ m c.pt ≫ c.π.app (op m) = 0`.
- The cokernel condition `hcok`: for every `m`, the projection
  `c.π.app (op m)` is a cokernel of `powSMul ℓ m c.pt` (an `IsColimit` of the
  cokernel cofork). Given `hcok`:
  - `reductionIso c hcok m : c.pt / ℓ ^ m c.pt ≅ T m`, the comparison of the
    two cokernels, with `reductionπ_reductionIso_hom`:
    `reductionπ ℓ c.pt m ≫ (reductionIso c hcok m).hom = c.π.app (op m)`;
  - `reductionTowerIso c hcok : reductionTower ℓ c.pt ≅ T.tower`, the
    isomorphism of inverse systems with these components
    (`reductionTowerIso_hom_app`). It does not compare the maps `i` of `T`
    with those of the published `reductionSystem`, and is an isomorphism of
    towers, not of `ℓ`-divisible systems;
  - `isLimitReductionConeOfIsLimit c hc hcok`: if `c` is a limit cone,
    `reductionCone ℓ c.pt` is a limit cone, so `c.pt` is the inverse limit of
    its own reductions `c.pt / ℓ ^ m c.pt`. Proof: `reductionCone ℓ c.pt`
    followed by `reductionTowerIso` is `c`, up to the identity of the vertex.
- `isCokernelOfExact c m hex hepi`: the cokernel condition at `m` from
  exactness of `c.pt → c.pt → T m` (first map `ℓ ^ m`, second the
  projection) and the projection being an epimorphism.
- For an additive, faithful functor `F : C ⥤ D` to an abelian category that
  preserves finite limits and finite colimits: `exact_of_map`, the exactness
  above holds for `c` when it holds for `F.mapCone c` over the published
  `T.map F`; `isCokernelOfMap`, the cokernel condition for `c` from exactness
  and epimorphisms for `F.mapCone c`.
- `exact_powSMul_π`, `epi_π`, `isCokernelOfIsLimit`: for a limit cone over a
  system of modules, the exactness, the epimorphisms, and hence the cokernel
  condition hold (from `π_hom_apply_eq_zero_iff` and `π_surjective`).

## Functors to modules; representations

Let `F : C ⥤ ModuleCat R` be additive, faithful, preserving finite limits,
finite colimits and limits indexed by `ℕᵒᵖ`, and let `c` be a limit cone
(`hc`). Then `F.mapCone c` is a limit cone over `T.map F`, so:

- `isCokernelOfFaithful hc F`: the cokernel condition for `c`;
- `reductionTowerIsoOfFaithful hc F : reductionTower ℓ c.pt ≅ T.tower` and
  `isLimitReductionConeOfFaithful hc F : IsLimit (reductionCone ℓ c.pt)`;
- `mono_powSMul_one_of_faithful hc F`: `powSMul ℓ 1 c.pt` is a monomorphism
  (multiplication by `ℓ` on `F.obj c.pt` is injective, and `F` reflects
  monomorphisms). This is the hypothesis `[Mono (powSMul ℓ 1 L)]` of the
  published `reductionSystem`.

For representations of a monoid `G` (`Rep.{w} R G`, with the forgetful functor
to `ModuleCat.{w} R`):

- instance `rep_forget₂_preservesLimitsOfShape_nat`: the forgetful functor
  preserves limits indexed by `ℕᵒᵖ` (from Mathlib's preservation of limits of
  size `w`), so the results above apply with `F` the forgetful functor;
- `rep_π_hom_apply_eq_zero_iff`, `rep_π_surjective`, `rep_isSMulRegular`,
  `rep_isAdicComplete`: the statements `π_hom_apply_eq_zero_iff`,
  `π_surjective`, `isSMulRegular_of_isLimit` and `isAdicComplete_of_isLimit`
  for the vertex of a limit cone in `Rep R G`, with its underlying module.

## Representations with the inverse limit topology

Here `G` is a group, `R : Type u`, and
`T : DivisibleSystem (Action (ModuleCat.{u} R) G) ℓ`. The published
`ContinuousLimit.ConeSpace c` is the underlying module of `c.pt` with the
inverse limit topology of the levels `T m` with the discrete topology, and
`proj c (op m) : ConeSpace c →ₗ[R] T m` is the projection. The forgetful
functor `Action.forget` to `ModuleCat R` satisfies the hypotheses on `F`
above (Mathlib instances), so the results of the previous section apply with
`F = Action.forget (ModuleCat R) G`.

- `ker_proj hc m`: `LinearMap.ker (proj c (op m)) = (ℓ) ^ m • ConeSpace c`.
- `isSMulRegular_coneSpace hc`, `isAdicComplete_coneSpace hc`: no `ℓ`-torsion;
  `ℓ`-adically complete and Hausdorff.
- `topology_eq_adicModuleTopology hc`: the topology of `ConeSpace c` equals
  `(Ideal.span {ℓ}).adicModuleTopology (ConeSpace c)`, Mathlib's `ℓ`-adic
  topology, whose neighbourhoods of `0` have the basis `(ℓ) ^ n • ⊤`. Proof:
  both are additive group topologies (`IsTopologicalAddGroup.ext`), so it
  suffices to compare neighbourhoods of `0`. For the inverse limit topology
  they form the infimum over `m` of the principal filters of the kernels of
  `proj c (op m)`, which are `(ℓ) ^ m • ⊤` by `ker_proj`; this decreasing
  family is a basis. For the `ℓ`-adic topology the sets of the module filter
  basis are exactly the `(ℓ) ^ n • ⊤`.
- `continuous_action_adicModuleTopology hc hT`: if `G` is a topological
  space with continuous multiplication and every level is smooth (`hT`,
  stated for `(Rep.ActionToRep R G).obj (T.tower.obj j)` as in the published
  `ContinuousLimit.continuous_action`), the action map
  `G × ConeSpace c → ConeSpace c` is continuous when `ConeSpace c` carries the
  `ℓ`-adic topology (on both factors where it occurs; the statement installs
  `adicModuleTopology` as a local instance). Proof: rewrite with
  `topology_eq_adicModuleTopology` and apply `continuous_action`.

## Harris's degree-zero étale cohomology

The variables are those of the published `harrisEtaleAdicCohomology`: `ℓ`
with `[NeZero ℓ]`, Harris's datum `ρ`, the place `p`, the level `U`, a scheme
`X`, a diagram `Y` of finite étale torsors and `hY`. `hΓ` is the hypothesis of
the published `harrisEtaleSectionsDivisibleSystem`: global sections
`Γ(X, -)` of the transition maps of Harris's étale system
`harrisEtaleDivisibleSystem` (the sheaves `𝓛 / ℓ ^ m` of the published
model) are epimorphisms. `R` below is `HarrisCoefficientIntegers L p`.

- `harrisEtaleAdicCohomologyZeroCone`: the cone over
  `(harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ).tower` (which is
  `harrisEtaleSectionsSystem`, the modules `Γ(X, 𝓛 / ℓ ^ m)`) with vertex
  `harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0 = lim_m H^0(X, 𝓛 / ℓ ^ m)`,
  obtained from the limit cone by the published isomorphism
  `harrisEtaleAdicCohomologyZeroDivisibleIso` (`Cone.extend`);
  `harrisEtaleAdicCohomologyZeroConeIsLimit`: it is a limit cone
  (`IsLimit.extendIso`).
- `isSMulRegular_harrisEtaleAdicCohomology_zero`,
  `isAdicComplete_harrisEtaleAdicCohomology_zero`: under `hΓ`, the module
  `lim_m H^0(X, 𝓛 / ℓ ^ m)` has no `ℓ`-torsion and is `ℓ`-adically complete
  and Hausdorff.
- `harrisEtaleAdicCohomologyZeroReductionIso`: under `hΓ`,
  `reductionTower ℓ (harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0) ≅
  harrisEtaleSectionsSystem ρ p U ℓ X Y hY`: the reductions of
  `lim_m H^0(X, 𝓛 / ℓ ^ m)` modulo `ℓ ^ m` are the modules `Γ(X, 𝓛 / ℓ ^ m)`,
  compatibly with the transition maps (`reductionTowerIso` with
  `isCokernelOfIsLimit`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2 (Worker 61 read the scanned
pages):

- printed p.304 (one-based PDF page 6): "By an ℓ-divisible system of
  S(ẽ)-modules over U(ẽ) we mean a collection {T_m} of étale sheaves in smooth
  ℤ/ℓ^mℤ[S(ẽ)]-modules over U(ẽ), m ≥ 1, with morphisms
  i = i_{m',m} : T_{m'} → T_m and j = j_{m,m−m'} : T_m → T_{m−m'}, for all
  m > m' ≥ 1 such that T_m is free over ℤ/ℓ^mℤ, i identifies T_{m'} with the
  p^{m'}-torsion in T_m, and (2.1) 0 → T_{m'} → T_m → T_{m−m'} → 0 is exact."
  The published `DivisibleSystem` reads the printed `p^{m'}` as `ℓ^{m'}` and
  replaces freeness over `ℤ/ℓ^mℤ` by the flatness condition (see its
  Markdown); this module uses only the published axioms.
- printed p.306 (one-based PDF page 8): the system of complexes
  `{C_m^•(U(ẽ)_F̄)}` "satisfies a Mittag-Leffler condition [EGA III, Chap. 0,
  Proposition 13.2.3], hence that Lemma 2.8. For every q, there is a
  canonical isomorphism H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)."

Milne, *Étale Cohomology* (1980), Chapter V, §1, printed p.164 (one-based PDF
page 178; Worker 61 read the text layer of the scanned page), for an `l`-adic
sheaf `F = (F_n)`: "the action of `π₁(X, x)` on `F_x = lim (F_n)_x` need not
factor through a finite quotient. However, the action is continuous when
`F_x` is given the `l`-adic topology".

Interpretation. Harris takes inverse limits over `m` of `ℓ`-divisible systems
(Lemma 2.8; the integral cohomology `H^q(X, 𝓛̃) = lim_m H^q(X, 𝓛_m)` of §4,
modelled by the published `EtaleAdicCohomology`) but states no property of
these limits. The facts proved here (no `ℓ`-torsion, `ℓ`-adic completeness,
the reductions modulo `ℓ ^ m` recover the levels) are the standard
description of such a limit as an `ℓ`-adically complete torsion-free module
with the given reductions; we prove them from the published axioms, as our
reading of Harris's passage to the limit. For Milne's remark, the published
`ContinuousLimit` proved continuity of the action for the inverse limit
topology of the discrete levels and left its comparison with the `ℓ`-adic
topology open; `topology_eq_adicModuleTopology` makes this comparison for
inverse limits of `ℓ`-divisible systems, so that
`continuous_action_adicModuleTopology` states continuity in Milne's
`l`-adic topology for such limits. The statements, the formulation through
`IsAdicComplete`, `IsSMulRegular` and `adicModuleTopology`, and all proofs
are ours; the module is derived.

## Scope

The module concerns inverse limits of `ℓ`-divisible systems only. It does not
compare the inverse limit topology with the `ℓ`-adic topology for other
inverse systems (for example arbitrary finitely generated `ℤ_ℓ`-modules
presented differently), prove compactness, or treat `ℚ_ℓ`-coefficients or
continuous cohomology. The tower isomorphisms do not compare the maps `i` of
an `ℓ`-divisible system with those of the published `reductionSystem` (the
published axioms determine `i` only up to an automorphism of `T m'`). The
étale results are in degree zero only, under the explicit surjectivity
hypothesis `hΓ`; Harris's derivation of such surjectivity, cohomology in
positive degrees, and the identification of `X`, `Y` and the groups acting
with Harris's Shimura varieties are not formalized. Smoothness of levels
stays an explicit hypothesis (`hT`). The topological results require the
carriers in the universe of `R`, as in the published `ContinuousLimit`. No
bridge to the published `Langlands.Cohomology.Continuous` modules (for
example `DiscreteModule`) is built.

Source registrations: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; Milne
1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
