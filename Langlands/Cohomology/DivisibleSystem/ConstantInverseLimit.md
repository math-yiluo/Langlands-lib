# `ℓ`-adic limits of the truncated constant Godement section systems

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem.ConstantTruncation` (Worker 61): the
  truncated smooth Godement resolution systems
  `smoothGodementTruncatedResolutionSystem h T D` and their inclusions
  `smoothGodementTruncatedResolutionHom h T D` into
  `smoothGodementResolutionSystem h T`; the section systems
  `smoothGodementTruncatedSectionsSystem h T D Φ hterm hres` and
  `isZero_smoothGodementTruncatedSectionsSystem_obj_X`; the constant cases
  `constantGodementTruncatedSectionsSystem`,
  `constantGodementTruncatedCompactSectionsSystem`, `constantLevelSheaf` and
  `intConstantGodementTruncatedSectionsSystem`; and
  `smoothGodementResolutionSystemObjIsoOfIso`. Through it: the generic
  `truncation`, `truncationHom`, `truncationInclusion`,
  `isIso_truncationInclusion_tower_app` and
  `mono_truncationInclusion_tower_app` (Truncation module), the systems
  `truncatedResolutionSystem`, `truncatedResolutionHom`,
  `truncatedResolutionSectionsSystem` and `resolutionSystem` (Truncation,
  Sections and Resolution modules), `residualInclusion_termDifferential_tower_app`
  (Coaugmented module), `constantSheafSystem`, `intConstantSheafSystem`,
  `constantGodementResolutionSystem`, `constantGodementResolutionSystemObjIso`
  and `intConstantSheafSystemObjIso` (ConstantCoefficients module), the
  compact sections functor `smoothSheafCompactSections R G X` and the smooth
  Godement complex `smoothComplex R G X F`.
- `Langlands.Cohomology.DivisibleSystem.InverseLimit` (Worker 61):
  `inverseLimit`, `inverseLimitHomologyComparison` and
  `inverseLimitHomologyComparison_π`,
  `isIso_inverseLimitHomologyComparison_of_finite`,
  `isIso_inverseLimitHomologyComparison_rep`,
  `finite_homology_extend_embeddingUpNat`, and Harris's Lemma 2.8:
  `quotientInvariantsInverseLimit`,
  `quotientInvariantsInverseLimitComparison` and
  `isIso_quotientInvariantsInverseLimitComparison`. Through it: `extendSystem`
  (TotalComparison module), `mapResidualInclusionIsKernel` (LeftExact module),
  `toRepComplexes` and `smoothQuotientInvariants`
  (Invariants module), `quotientProjection` (InvariantTransition module),
  `IsProPSubgroup` (ProPInvariants module), and Worker 3's unproved statements
  `FiniteCohomologyInverseLimitStatement`
  (`Langlands.Cohomology.InverseLimit.Statement`) and
  `ProPInvariantSubcomplexStatement`
  (`Langlands.Cohomology.ProPInvariants.Statement`), which appear only as
  hypotheses.

From Mathlib it uses `PadicInt`, `PadicInt.isUnit_iff`,
`PadicInt.norm_natCast_eq_one_iff`, `PadicInt.toZModPow`,
`PadicInt.ker_toZModPow`, `ZMod.ringHom_surjective`, `Ideal.quotEquivOfEq`,
`RingHom.quotientKerEquivOfSurjective`, `IsRegular.of_ne_zero`,
`Nat.coprime_primes`, `limMap`, `limit.post`, `lim.mapIso`,
`IsLimit.conePointUniqueUpToIso`, `KernelFork.isLimitOfIsLimitOfIff'`,
`ShortComplex.cyclesIsKernel`, `ShortComplex.isIso_iCycles`,
`ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi`, `quasiIsoAt_iff'`,
`HomologicalComplex.homologyFunctor`, `HomologicalComplex.extend`,
`ComplexShape.embeddingUpNat` and its `extendFunctor`, `extendHomologyIso`,
`extendHomologyIso_hom_naturality`, `extend_exactAt`, `quasiIsoAt_iff`,
`ShortComplex.quasiIso_of_epi_of_isIso_of_mono`,
`Functor.mapHomologicalComplex`, `Functor.whiskerRight` and
`NatIso.isIso_of_isIso_app`.

All names below are in the namespace `Langlands.Cohomology`. The names from
the section "`ℓ`-adic limits" on are in `Langlands.Cohomology.DivisibleSystem`.
Composition `f ≫ g` is `f` followed by `g`. For a system `K`, `K m` is the
complex at level `m`. `H^n` is the degree-`n` cohomology `homology n` of a
cochain complex, and `lim_m` is the limit over `ℕᵒᵖ`, i.e. the inverse limit
over `m`.

## Finiteness for modules

`R` is a ring.

- `finite_of_moduleCat_iso e h`: if `X ≅ Y` in `ModuleCat R` and `X` is
  finite, so is `Y`.
- `finite_of_moduleCat_isZero h`: a zero object of `ModuleCat R` is finite.
- `finite_homology_extend_embeddingUpNat_moduleCat X h q`: if an `ℕ`-graded
  cochain complex `X` of `R`-modules has finite cohomology in every degree, so
  does its extension by zero to `ℤ` along `ComplexShape.embeddingUpNat`, in
  every degree `q : ℤ`. This is the module counterpart of the published
  `finite_homology_extend_embeddingUpNat` for representations, with the same
  proof: for `q = n ≥ 0` use `extendHomologyIso`; for `q < 0` the extension
  is exact at `q`.

## A quasi-isomorphism criterion for short complexes

`C` is an abelian category.

- `quasiIso_of_epi_of_isLimit_kernelFork φ hg hc e he`: let `φ : S₁ ⟶ S₂` be a
  morphism of short complexes with `φ.τ₁` an epimorphism and `S₁.g = 0`. Let
  `i : K ⟶ S₂.X₂` be a kernel of `S₂.g` (`hc`) and `e : S₁.X₂ ≅ K` an
  isomorphism with `φ.τ₂ = e.hom ≫ i` (`he`). Then `φ` is a
  quasi-isomorphism. Proof: since `S₁.g = 0`, the inclusion of the cycles of
  `S₁` is an isomorphism. The map induced on cycles is that isomorphism
  followed by `e` and by the comparison of the two kernels `i` and
  `S₂.iCycles` of `S₂.g`, so it is an isomorphism. Mathlib's
  `isIso_homologyMap_of_isIso_cyclesMap_of_epi` then applies, `φ.τ₁` being an
  epimorphism.

## Limits of homology

`C` is an abelian category, `c` a complex shape on `ι`, and `J` a category
such that `C` has limits of shape `J`. `K, L : J ⥤ HomologicalComplex C c`
are diagrams of complexes and `α : K ⟶ L`.

- `limitHomologyMap α q`: the morphism
  `limit (K ⋙ H_q) ⟶ limit (L ⋙ H_q)` induced by `α`, where `H_q` is the
  degree-`q` homology functor. It is `limMap` of `α` whiskered by `H_q`.
- `limitHomologyMap_π`: followed by the projection to `j`, it is the
  projection to `j` followed by the map on homology induced by `α.app j`.
- `isIso_limitHomologyMap α q hα`: if every `α.app j` is a
  quasi-isomorphism in degree `q`, then `limitHomologyMap α q` is an
  isomorphism. Every component of the whiskered transformation is then an
  isomorphism, and `limMap` of a natural isomorphism is an isomorphism.
- `limit_post_comp_limitHomologyMap α q`: naturality of the comparison
  `limit.post K H_q : H_q(lim K) ⟶ lim (K ⋙ H_q)`. It is followed by
  `limitHomologyMap α q` equals `H_q(limMap α)` followed by
  `limit.post L H_q`. This is checked on the limit projections.

## Cohomology of the extension by zero

- `extendHomologyNatIso C n`: for an abelian category `C` and `n : ℕ`, the
  natural isomorphism between "extend an `ℕ`-graded cochain complex by zero to
  `ℤ`, then take `H^n`" and "take `H^n`". Its components are Mathlib's
  `extendHomologyIso` (`extendHomologyNatIso_hom_app`). Naturality is Mathlib's
  `extendHomologyIso_hom_naturality`.

## `ℓ`-adic limits

`E` is an abelian category with limits of shape `ℕᵒᵖ`, and `K` is an
`ℓ`-divisible system of `ℕ`-graded cochain complexes in `E`
(`DivisibleSystem (CochainComplex E ℕ) ℓ`). `K.extendSystem` is the published
system of the levels extended by zero to `ℤ`.

- `adicLimit K` (`abbrev`): `lim_m K m` as a `ℤ`-graded complex, namely the
  published `inverseLimit` of `K.extendSystem`.
- `levelCohomologyLimit K n` (`abbrev`): `lim_m H^n(K m)`, the limit of the
  tower `m ↦ H^n(K m)`.
- `extendLevelCohomologyLimitIso K n`: the limit of the degree-`n`
  cohomologies of the extended levels is `levelCohomologyLimit K n`. It is the
  limit of the components of `extendHomologyNatIso`
  (`extendLevelCohomologyLimitIso_hom_π`).
- `adicLimitComparison K n : H^n(adicLimit K) ⟶ levelCohomologyLimit K n`: the
  published comparison `inverseLimitHomologyComparison` of `K.extendSystem` in
  degree `n`, followed by `extendLevelCohomologyLimitIso`. By
  `adicLimitComparison_π`, followed by the projection to level `m` it is the map
  induced on `H^n` by the limit projection, followed by the identification of
  `H^n` of the extended level with `H^n(K m)`.
- `isIso_adicLimitComparison_of_finite hS K hfin n`: for an `ℓ`-divisible
  system of `ℕ`-graded complexes of `R`-modules whose levels have finite
  cohomology in every degree (`hfin`), given
  `hS : FiniteCohomologyInverseLimitStatement R`, the comparison is an
  isomorphism in every degree `n`. Proof: the extended levels have finite
  cohomology (`finite_homology_extend_embeddingUpNat_moduleCat`), so the
  published `isIso_inverseLimitHomologyComparison_of_finite` applies to
  `K.extendSystem`.
- `isIso_adicLimitComparison_rep hS K hfin n`: the same for complexes of
  representations in `Rep k G` (commutative ring `k`, monoid `G`), given
  `FiniteCohomologyInverseLimitStatement k`. It uses
  `isIso_inverseLimitHomologyComparison_rep` and
  `finite_homology_extend_embeddingUpNat`.

## Sections of a truncation in low degrees

`C` and `E` are abelian categories, `Φ : C ⥤ E` is additive and preserves
finite limits, and `S`, `d`, `sq`, `D`, `Z`, `p`, `ι`, `hpι`, `hιd` are as in
the Truncation module. Thus `truncation …` has terms `S q` in degrees `≤ D`,
`Z` in degree `D + 1` and `0` above, and `truncationHom …` is its inclusion
into the complex of the `S q`.

- `map_truncationHom_quasiIsoAt_of_le … Φ m hq`: for `q ≤ D`, `Φ` applied
  degreewise to the level-`m` component of `truncationHom` is a
  quasi-isomorphism in degree `q`. Proof: on the short complex at `q`, the
  three components are `Φ` of inclusion components in degrees `prev q ≤ D`,
  `q ≤ D` and `q + 1`. The first two are `Φ` of isomorphisms. The third is
  `Φ` of a monomorphism, and `Φ` preserves monomorphisms because it preserves
  finite limits. `ShortComplex.quasiIso_of_epi_of_isIso_of_mono` then applies.
  This is the published `truncationHom_quasiIsoAt_of_le` after a left exact
  functor. It needs no exactness of the sections functor and none of Harris's
  vanishing results.
- `map_truncationHom_quasiIsoAt_top … Φ m hker`: if `Φ` maps `ι` at level `m`
  to a kernel of `Φ` of the differential `S (D + 1) ⟶ S (D + 2)` (`hker`), the
  same map is a quasi-isomorphism in degree `D + 1`. Proof: at `D + 1` the
  truncated complex is `S D ⟶ Z ⟶ 0`, so `quasiIso_of_epi_of_isLimit_kernelFork`
  applies. Its first component is `Φ` of an isomorphism, its source has
  `g = 0`, and its middle component is `Φ` of the identification of the
  degree-`(D + 1)` term with `Z` followed by `Φ` of `ι`. This lemma does not
  use that `Φ` preserves finite limits; the kernel is the hypothesis `hker`.
- `map_truncationHom_quasiIsoAt_of_le_succ … Φ m hq hker`: the two previous
  lemmas combined, for degrees `q ≤ D + 1`. Above `D + 1` the truncated complex
  is zero, so no such statement holds in general.

## Section complexes of truncated resolutions

`F : C ⥤ C` is additive and exact with a monic coaugmentation
`η : 𝟭 C ⟶ F`, `T` is an `ℓ`-divisible system in `C`, and `D : ℕ`. `Φ` is as
above, and `hterm`, `hres` are the hypotheses of the published
`truncatedResolutionSectionsSystem`: `Φ` maps the projections of the term
systems `F^q` (`q ≤ D`) and of the residual system `R^(D + 1)` to
epimorphisms.

- `resolutionSectionsTower F η T Φ` (`abbrev`): the tower
  `m ↦ Φ(F_m^•)` of `Φ` applied degreewise to the resolution system. It is a
  functor `ℕᵒᵖ ⥤ CochainComplex E ℕ`. No surjectivity of its transition maps is
  assumed, so it is only an inverse system, not an `ℓ`-divisible system.
- `truncatedResolutionSectionsTowerHom F η T D Φ hterm hres`: the morphism of
  towers from the truncated section complexes to `resolutionSectionsTower`, `Φ`
  applied degreewise to `truncatedResolutionHom`
  (`truncatedResolutionSectionsTowerHom_app`).
- `map_truncatedResolutionHom_quasiIsoAt` and
  `truncatedResolutionSectionsTowerHom_quasiIsoAt`: at every level, these maps
  are quasi-isomorphisms in degrees `≤ D + 1`. This is
  `map_truncationHom_quasiIsoAt_of_le_succ`. The kernel hypothesis is the
  published `mapResidualInclusionIsKernel`: `Φ` maps the residual inclusion
  `R^(D + 1) ⟶ F^(D + 1)` to a kernel of `Φ(F^(D + 1)) ⟶ Φ(F^(D + 2))`.
- `truncatedResolutionSectionsAdicCohomologyIso … hn` (with
  `HasLimitsOfShape ℕᵒᵖ E`): for `n ≤ D + 1`, the isomorphism from
  `levelCohomologyLimit` of the truncated section complexes to
  `lim_m H^n(Φ(F_m^•))` given by `limitHomologyMap`.

## Smooth Godement section complexes

`R` is a commutative ring, `G` a topological group, `X` a topological space
with a `G`-action by homeomorphisms and `HasStableNeighbourhoods G X`, all in
one universe `u`. `T : SmoothSheafDivisibleSystem R G X ℓ`, `D : ℕ`, and
`h : SmoothGodementZeroExactStatement R G X` is Worker 3's unproved exactness
statement for the degree-zero smooth Godement functor (an explicit
hypothesis). `Φ` is an additive sections functor on smooth sheaves preserving
finite limits, and `hterm`, `hres` are the surjectivity hypotheses of
`smoothGodementTruncatedSectionsSystem h T D Φ hterm hres`.

- `smoothGodementSectionsTower h T Φ` (`abbrev`): the tower `m ↦ Φ(F_m^•)` of
  `Φ` applied degreewise to the smooth Godement resolutions of the levels of
  `T`, with no surjectivity assumption.
- `smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres`, with
  `smoothGodementTruncatedSectionsTowerHom_app`: `Φ` applied degreewise to
  `smoothGodementTruncatedResolutionHom h T D`, as a morphism of towers from the
  truncated section complexes `{G_m^•(U)}` to `smoothGodementSectionsTower`.
- `smoothGodementTruncatedSectionsTowerHom_quasiIsoAt`: at every level this is
  a quasi-isomorphism in degrees `≤ D + 1`.
- `smoothGodementTruncatedSectionsAdicCohomologyIso … hn`, with
  `smoothGodementTruncatedSectionsAdicCohomologyIso_hom_π`: for `n ≤ D + 1`,
  `lim_m H^n(G_m^•(U)) ≅ lim_m H^n(Φ(F_m^•))`, induced by the inclusions.
- `smoothGodementTruncatedSectionsAdicLimitHomologyIso h T D Φ hterm hres hS
  hfin hn`: for `Φ` with values in `ModuleCat R'` (any ring `R'`),
  `FiniteCohomologyInverseLimitStatement R'` (`hS`) and finite cohomology of
  every level of the truncated section complexes (`hfin`), for `n ≤ D + 1` it is
  `H^n(lim_m G_m^•(U)) ≅ lim_m H^n(Φ(F_m^•))`. It is the forward comparison
  `adicLimitComparison`, made an isomorphism by
  `isIso_adicLimitComparison_of_finite`, followed by
  `smoothGodementTruncatedSectionsAdicCohomologyIso`.
- `smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep`: the same for `Φ`
  with values in `Rep k G'` (commutative ring `k`, monoid `G'`), given
  `FiniteCohomologyInverseLimitStatement k`.

## Harris's Lemma 2.8 for the truncated Godement compact sections

`R`, `G`, `X`, `h`, `T` and `D` are as in the previous section. `hterm` and
`hres` are the surjectivity hypotheses for compact sections, and
`K = smoothGodementTruncatedCompactSectionsSystem h T D hterm hres` is the
published system `{G_m^•(U)}` of compact-section complexes, in
`SmoothRep.{u, u, u} R G`. The remaining variables are those of the published
Lemma 2.8. `ι : Type u` is a filtered preorder, and `H` is an antitone family
of normal subgroups of finite index. `hK` says that `H i`-invariants of the
projections of `K` stay epimorphisms. `hk` says that the orders of the kernels
of the transition maps `G ⧸ H j → G ⧸ H i` are units in `R`.

- `isZero_smoothGodementTruncatedCompactSectionsSystem_obj_X`: every level of
  `K` is zero in degrees `≥ D + 2`. This is the published vanishing above
  `D + 1`, and it discharges the hypothesis `hN` of the published Lemma 2.8
  with `N = D + 2`.
- `smoothGodementCompactSectionsRepTower h T` (`abbrev`): the tower
  `m ↦ Γ_c(F_m^•)` of compact sections of the full smooth Godement resolutions,
  as complexes of representations, i.e. after `SmoothRep.toRep`.
- `smoothGodementCompactSectionsRepTowerHom`: the inclusion from the tower of
  `K.toRepComplexes` into `smoothGodementCompactSectionsRepTower`, which is
  compact sections and then `toRep` applied degreewise to
  `smoothGodementTruncatedResolutionHom`. By
  `smoothGodementCompactSectionsRepTowerHom_quasiIsoAt`, at every level it is a
  quasi-isomorphism in degrees `≤ D + 1`: apply
  `map_truncatedResolutionHom_quasiIsoAt` with `Φ` the composite.
- `smoothGodementQuotientInvariantsInverseLimit … H hH hK hk` (`abbrev`): our
  `lim C_m^•` for `K`, the published `quotientInvariantsInverseLimit` with
  `N = D + 2` and universe parameter `w = 0`, a `ℤ`-graded complex in
  `Rep R G`.
- `smoothGodementQuotientInvariantsInverseLimitComparison … q` (`abbrev`): the
  published map of Lemma 2.8, from `H^q(lim C_m^•)` to
  `lim_m H^q` of the extended complexes `K.toRepComplexes`.
- `isIso_smoothGodementQuotientInvariantsInverseLimitComparison … hS hS' hP hR
  htriv hfin q`: the published `isIso_quotientInvariantsInverseLimitComparison`
  for `K`. Its hypotheses are `ProPInvariantSubcomplexStatement` (`hS`) and
  `FiniteCohomologyInverseLimitStatement R` (`hS'`). Every `H i` must be a
  pro-`p` subgroup (`hP`) with `p` a unit in `R` (`hR`), act trivially on the
  cohomology of every level of `K` (`htriv`), and that cohomology must be
  finite (`hfin`).
- `smoothGodementQuotientInvariantsInverseLimitHomologyIso … hn`: under the
  same hypotheses, for `n ≤ D + 1`, `H^n(lim C_m^•) ≅ lim_m H^n(Γ_c(F_m^•))`. It is
  the forward Lemma 2.8 comparison, made an isomorphism by
  `isIso_smoothGodementQuotientInvariantsInverseLimitComparison`, then
  `extendLevelCohomologyLimitIso`, then the isomorphism `limitHomologyMap` of
  `smoothGodementCompactSectionsRepTowerHom`.

## The constant systems `{R / ℓ ^ m R}`

Here `R`, `G`, `X` and `h` are as above, `hℓ : IsSMulRegular R (ℓ : R)`, and
`T` is the published constant system `constantSheafSystem hℓ G X` of the
locally constant sheaves of the trivial smooth representations
`R / ℓ ^ m R`.

- `constantGodementSectionsTower hℓ G X h Φ` (`abbrev`):
  `smoothGodementSectionsTower` for the constant system.
  `constantGodementSectionsTowerObjIso … m`: its level `m` is `Φ` applied
  degreewise to `smoothComplex R G X (constantLevelSheaf R ℓ G X m)`, the
  smooth Godement complex of the locally constant sheaf of `R / ℓ ^ m R` (`Φ`
  of `constantGodementResolutionSystemObjIso`).
- `constantGodementAdicCohomology hℓ G X h Φ n` (`abbrev`): the limit of the
  degree-`n` cohomologies of `constantGodementSectionsTower`, i.e.
  `lim_m H^n(Φ(F_m^•))`, our rendering of Harris's
  `lim_m H_c^n(U, R / ℓ ^ m R)` (see Provenance).
- `constantGodementAdicSectionsComplex hℓ G X h D Φ hterm hres` (`abbrev`):
  `adicLimit` of the truncated constant section complexes
  `constantGodementTruncatedSectionsSystem`, i.e. `lim_m G_m^•(U)`.
- `constantGodementAdicCohomologyIso … hn`: for `n ≤ D + 1`,
  `levelCohomologyLimit` of the truncated constant section complexes is
  `constantGodementAdicCohomology`.
- `constantGodementAdicLimitHomologyIso` (`Φ` with values in `ModuleCat R'`)
  and `constantGodementAdicLimitHomologyIsoRep` (`Φ` with values in
  `Rep k G'`): given `FiniteCohomologyInverseLimitStatement` and finite level
  cohomology, for `n ≤ D + 1`,
  `H^n(constantGodementAdicSectionsComplex) ≅ constantGodementAdicCohomology`.
  The published invariant compact sections
  `SmoothSheafCohomology.invariantCompactSections R G X` are a case of the
  first.
- `constantQuotientInvariantsInverseLimit` (`abbrev`) and
  `constantQuotientInvariantsInverseLimitHomologyIso`: the Lemma 2.8 complex
  `lim C_m^•` and the isomorphism
  `H^n(lim C_m^•) ≅ lim_m H^n(Γ_c(F_m^•))` (`n ≤ D + 1`) for the constant system,
  with `K = constantGodementTruncatedCompactSectionsSystem`.

## The constant systems `{ℤ / ℓ ^ m ℤ}`

Here `ℓ ≠ 0`, `G` and `X` are in `Type`, `R = ℤ`, and `T` is the published
`intConstantSheafSystem ℓ hℓ G X`, with levels the locally constant sheaves of
`ZMod (ℓ ^ m)`.

- `intConstantGodementSectionsTower` (`abbrev`) and
  `intConstantGodementSectionsTowerObjIso … m`: the tower `m ↦ Φ(F_m^•)` and
  the identification of its level `m` with `Φ` of the smooth Godement complex
  of the locally constant sheaf of `ZMod (ℓ ^ m)` (along
  `smoothGodementResolutionSystemObjIsoOfIso` and
  `intConstantSheafSystemObjIso`).
- `intConstantGodementAdicCohomology` (`abbrev`): `lim_m H^n(Φ(F_m^•))`, our
  rendering of `lim_m H_c^n(U, ℤ / ℓ ^ m ℤ)`.
- `intConstantGodementAdicSectionsComplex` (`abbrev`): `lim_m G_m^•(U)`, the
  `adicLimit` of `intConstantGodementTruncatedSectionsSystem`.
- `intConstantGodementAdicLimitHomologyIso` and
  `intConstantGodementAdicLimitHomologyIsoRep`: for `n ≤ D + 1`,
  `H^n(lim_m G_m^•(U)) ≅ lim_m H^n(Φ(F_m^•))`, under the same hypotheses as in
  the general case.

There is deliberately no Lemma 2.8 case with coefficient ring `ℤ`. The
published Lemma 2.8 needs `p` to be a unit in the coefficient ring (`hR`) for a
family of pro-`p` subgroups, and the orders of the transition kernels to be
units (`hk`). Over `ℤ` the first forces `p = 1`, which contradicts the
primality in `IsProPSubgroup`, and the second forces all transition kernels to
be trivial. Harris's argument (p.305, after (2.3)) uses instead that
pro-`p` invariants are exact on `ℓ`-primary torsion modules for `p ≠ ℓ`. Here
this is realized by coefficients `ℤ_[ℓ]`, in which every `p` prime to `ℓ` is a
unit, and whose levels `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]` are the rings `ZMod (ℓ ^ m)`
(next section).

## `ℓ`-adic coefficients

Here `ℓ` is a prime (`[Fact ℓ.Prime]`), `ℤ_[ℓ]` is Mathlib's ring of `ℓ`-adic
integers `PadicInt ℓ`, and `G`, `X` are in `Type`.

- `padicInt_isSMulRegular ℓ`: `ℓ` is a non-zero-divisor in `ℤ_[ℓ]`
  (`ℤ_[ℓ]` is a domain of characteristic zero). This is the hypothesis `hℓ`
  of the constant systems for `R = ℤ_[ℓ]`.
- `padicInt_isUnit_natCast hn`: a natural number `n` prime to `ℓ` is a unit
  in `ℤ_[ℓ]` (its `ℓ`-adic norm is `1`, Mathlib's `PadicInt.isUnit_iff` and
  `PadicInt.norm_natCast_eq_one_iff`).
- `coprime_of_prime_ne hp hpℓ`: a prime `p ≠ ℓ` is prime to `ℓ`
  (`Nat.coprime_primes`).
- `padicLevelRingEquiv ℓ m`: the ring isomorphism
  `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ] ≃+* ZMod (ℓ ^ m)` induced by Mathlib's reduction
  `PadicInt.toZModPow m`. That reduction is surjective
  (`ZMod.ringHom_surjective`) with kernel `ℓ ^ m ℤ_[ℓ]` (`PadicInt.ker_toZModPow`).
  So the level rings of the constant system over `ℤ_[ℓ]` are Harris's
  `ℤ / ℓ ^ m ℤ`. Only the rings are identified here, not the sheaves.
- `padicConstantQuotientInvariantsInverseLimit ℓ G X h D hterm hres H hH hK hk`
  (`abbrev`): Harris's `lim C_m^•` with `ℓ`-adic coefficients, the case
  `R = ℤ_[ℓ]` of `constantQuotientInvariantsInverseLimit`. Here `hk` assumes
  only that the orders of the transition kernels are prime to `ℓ`. They are
  then units by `padicInt_isUnit_natCast`. In Harris's situation the kernels
  are finite `p`-groups with `p ≠ ℓ`.
- `padicConstantQuotientInvariantsInverseLimitHomologyIso … hS hS' hP hpℓ htriv
  hfin hn`: Harris's Lemma 2.8 with `ℓ`-adic coefficients in degrees
  `n ≤ D + 1`. The hypotheses are those of
  `constantQuotientInvariantsInverseLimitHomologyIso`, except that `hR` is
  replaced by `hpℓ : ℓ.Coprime p`.

These coefficient hypotheses are satisfiable. Worker 61 checked in a private
Lean probe that the trivial subgroup is pro-`3` and that `3` is a unit in
`ℤ_[2]`, by `padicInt_isUnit_natCast` and `coprime_of_prime_ne`. For a
constant family of subgroups the transition kernels are trivial, so `hk`
holds. The unproved statements `hS` and `hS'`, and the hypotheses on the
sheaves, remain assumptions.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306 (one-based PDF
pages 7–8). Worker 61 read both pages in the scanned original.

1. What Harris says. On p.305 Harris sets `G_m^• = τ^{≤D+1}(F_m^•)`. He notes
   that "it follows from Fact 2 that, for any m, the inclusion
   τ^{≤q}(F_m^•) → (F_m^•) is a quasi-isomorphism for q ≥ D". With
   `Z_m^q = ker d_m^q` and `B_m^q = im d_m^{q-1}` on the section complexes,
   he writes "(2.3) H_c^q(U(ẽ)_F̄, Z/ℓ^mZ) ≅ Z_m^q/B_m^q = H^q(G_m^•(U(ẽ)_F̄))".
   He then chooses "an open normal pro-p subgroup H ⊂ S(ẽ) that acts
   trivially on H_c^q(U(ẽ)_F̄, Z/ℓ^mZ) for all q and all m" and notes: "Since p
   is prime to ℓ, the functor H^0(H,•) is exact on ℓ-primary torsion
   modules".
   On p.306, after the comparison (2.6), he writes: "The maps
   j : C_m^•(U(ẽ)_F̄) → C_{m'}^•(U(ẽ)_F̄), for m > m', are all surjective by
   hypothesis. It thus follows from Fact 1 bis that the system of complexes
   {C_m^•(U(ẽ)_F̄)} satisfies a Mittag-Leffler condition [EGA III, Chap. 0,
   Proposition 13.2.3], hence that Lemma 2.8. For every q, there is a
   canonical isomorphism H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)."
2. What is formalized. The published InverseLimit module renders Lemma 2.8
   for a general system `K` of finite-length complexes of smooth
   representations, with right-hand side `lim_m H^q(K m)`, i.e. via (2.3).
   This module specializes it to `K = {G_m^•(U)}` with compact sections of the
   truncated smooth Godement resolutions, with `N = D + 2` proved rather than
   assumed, and to the constant systems `{R / ℓ ^ m R}`, in particular over
   `R = ℤ_[ℓ]`, whose levels are the rings `ℤ / ℓ ^ m ℤ`. The coefficient ring
   `ℤ_[ℓ]` replaces Harris's exactness of pro-`p` invariants on `ℓ`-primary
   torsion for `p ≠ ℓ` by the invertibility of `p` (see the section on
   `ℓ`-adic coefficients). It also constructs the `ℓ`-adic complex `lim_m G_m^•(U)` for any sections
   functor `Φ` and its comparison with `lim_m H^n`. Harris's inverse limits
   are over `m`. The `ℓ`-adic limit of `ℕ`-graded systems, extended to `ℤ`, is
   internal framework.
3. Our rendering of `H_c^n(U, ℤ/ℓ^mℤ)`. The Library has no derived-functor
   comparison for the smooth Godement resolution. Here
   `H^n(Γ_c(F_m^•))`, the cohomology of the compact sections of the smooth
   Godement resolution of the constant sheaf, stands for `H_c^n(U, ℤ/ℓ^mℤ)`,
   and `constantGodementAdicCohomology`, `intConstantGodementAdicCohomology`
   and the targets of the `…HomologyIso` maps for `lim_m H_c^n`. This is an
   interpretation, not Harris's definition. Harris's (2.3) identifies
   `H_c^n` with `H^n(G_m^•(U))` through the `RΓ_c`-acyclicity of the `G_m^q`,
   which is not proved here.
4. Derived content. The isomorphism `H^n(Φ(G_m^•)) ≅ H^n(Φ(F_m^•))` for
   `n ≤ D + 1` (`map_truncationHom_quasiIsoAt_of_le_succ`) is our elementary
   observation. It uses neither Fact 2 nor exactness of `Φ`, only that `Φ` is
   left exact, so that `Φ(G_m^{D+1})` is the kernel of
   `Φ(F_m^{D+1}) ⟶ Φ(F_m^{D+2})`. Harris's remark on p.305 concerns the sheaf
   complexes and uses Fact 2. Degrees above `D + 1` are not covered. The finite-cohomology route to the comparison is Worker 3's
   `FiniteCohomologyInverseLimitStatement`, as in the published InverseLimit
   module, in place of Harris's Mittag-Leffler argument.
5. What stays a hypothesis. These are explicit hypotheses:
   `SmoothGodementZeroExactStatement`; the surjectivity of the sections
   functors on the projections (`hterm`, `hres`) and of the `H i`-invariants
   (`hK`, Harris's "surjective by hypothesis"); the inverse-limit and pro-`p`
   statements (`hS`, `hS'`); the unit hypotheses on `p` and on the orders of
   the transition kernels (`hR`, `hk`), or over `ℤ_[ℓ]` their coprimality to
   `ℓ` (`hpℓ`, `hk`); and the finiteness (Fact 1 bis) and trivial action
   (`htriv`) of the level cohomology. Reading `G` as `S(ẽ)` and `X` as
   `U(ẽ)` is our interpretation, as in the parent modules. The Library's
   sheaves are equivariant sheaves on topological spaces, not étale sheaves
   on rigid analytic spaces.

## Scope

The module constructs the `ℓ`-adic complexes and the comparison maps, and
proves the low-degree truncation isomorphisms. It proves no acyclicity,
finiteness, Mittag-Leffler or vanishing statement for the constant sheaves,
and no `ℤ_ℓ`-module structure on the limits beyond what the categories
provide. It does not formalize (2.3), Fact 1 bis, Fact 2, or the
identification of `lim C_m^•` with `ℤ_ℓ`-coefficient étale cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
