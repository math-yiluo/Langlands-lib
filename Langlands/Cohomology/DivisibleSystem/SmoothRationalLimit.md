# Integral and rational structures on the `ℓ`-adic limits of smooth Godement towers

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit` (Worker 61):
  the `ℓ`-adic limit `adicLimit`, the limit of level cohomologies
  `levelCohomologyLimit`, the comparison `adicLimitComparison` with
  `adicLimitComparison_π`, `isIso_adicLimitComparison_of_finite` and
  `isIso_adicLimitComparison_rep`, the natural isomorphism
  `extendHomologyNatIso`; the smooth Godement towers
  `smoothGodementSectionsTower`, the isomorphisms
  `smoothGodementTruncatedSectionsAdicLimitHomologyIso` and
  `smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep`; the Lemma 2.8
  objects `smoothGodementQuotientInvariantsInverseLimit`,
  `smoothGodementQuotientInvariantsInverseLimitHomologyIso` and
  `smoothGodementCompactSectionsRepTower`; and the `ℓ`-adic coefficient
  results `padicInt_isSMulRegular`, `padicInt_isUnit_natCast`,
  `constantGodementAdicSectionsComplex` and
  `padicConstantQuotientInvariantsInverseLimit`. Through it: the base module
  `Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`, `mapFunctor`,
  `forget`), `mapHomologicalComplexHomologyIso` (InverseLimit module),
  `smoothGodementTruncatedSectionsSystem`, `smoothGodementTermSystem`,
  `smoothGodementResidualSystem`,
  `smoothGodementTruncatedCompactSectionsSystem`,
  `constantGodementTruncatedSectionsSystem` and
  `constantGodementTruncatedCompactSectionsSystem` (ConstantTruncation module),
  `constantSheafSystem` (ConstantCoefficients module),
  `smoothSheafCompactSections`, `smoothQuotientInvariants`,
  `quotientProjection`, `IsProPSubgroup`, and Worker 3's unproved statements
  `FiniteCohomologyInverseLimitStatement`,
  `ProPInvariantSubcomplexStatement` and `SmoothGodementZeroExactStatement`,
  which appear only as hypotheses.
- `Langlands.Cohomology.HyperextScalarExtension` (Worker 61): the instance
  `repExtendScalars_preservesHomology` (extension of scalars of
  representations along a flat algebra preserves homology). Through it,
  `Langlands.Cohomology.DivisibleSystem.ScalarExtension` (Worker 61):
  `repExtendScalars`, `repRestrictScalars`, `repExtendScalarsUnit` (with
  components `v ↦ 1 ⊗ v`), `repExtendScalarsComplex` and
  `quotientInvariantsInverseLimitBaseChange`.

From Mathlib it uses `ModuleCat.extendScalars`, `ModuleCat.restrictScalars`,
`ModuleCat.extendRestrictScalarsAdj`, `ModuleCat.ExtendScalars.hom_ext`,
`TensorProduct.tmul_add`, `RingHom.toAlgebra`, `Module.Flat`,
`Module.Flat.lTensor_exact`, `RingHom.flat_algebraMap_iff`,
`Algebra.algebraMap_self`, `LinearMap.exact_iff`,
`ShortComplex.moduleCat_exact_iff_range_eq_ker`,
`Functor.preservesHomology_of_map_exact`, `Functor.mapHomologicalComplex`,
`HomologicalComplex.homologyFunctor`, `ComplexShape.embeddingUpNat` and its
`extendFunctor`, `lim`, `limMap_π`, `limit.hom_ext`,
`Functor.whiskeringRight`, `Functor.whiskerRight`, `Functor.isoWhiskerLeft`,
`Functor.associator`, `Functor.map_isIso`, `Functor.mapIso`, `asIso`,
`NatTrans.ext`, `PadicInt` (`ℤ_[ℓ]`), `Padic` (`ℚ_[ℓ]`), the instance
`PadicInt.isFractionRing`, `nonZeroDivisors` and `IsLocalization.flat`.

All names below are in the namespace `Langlands.Cohomology.DivisibleSystem`.
Composition `f ≫ g` is `f` followed by `g`. For a system `K`, `K_m` is its
complex at level `m`. `H^n` is the degree-`n` cohomology `homology n` of a
cochain complex, and `lim_m` is the limit over `ℕᵒᵖ`, i.e. the inverse limit
over `m`. Extension of scalars along an algebra `R → S` is Mathlib's
`ModuleCat.extendScalars (algebraMap R S)`, which sends an `R`-module `M` to
`S ⊗_R M` with `S` acting on the first factor, or for representations the
published `repExtendScalars R S G` (`S ⊗_R V`, with `G` acting on the second
factor). This is the convention of the published EtaleRationalCohomology and
ScalarExtension modules. Harris writes `M ⊗ ℚ_ℓ`; no isomorphism between the
two orders of the factors is used or formalized here. For a complex `K`,
`S ⊗_R K` is the degreewise extension of scalars
(`Functor.mapHomologicalComplex`).

## The `ℓ`-adic limit as a functor

`E` is an abelian category (`E : Type u'`, morphisms in `Type v'`) with limits
of shape `ℕᵒᵖ`, and `ℓ : ℕ`. The objects are `ℓ`-divisible systems of
`ℕ`-graded cochain complexes in `E` and their morphisms (morphisms of towers
commuting with the inclusions).

- `adicLimitFunctor E ℓ`: the published `mapFunctor` of the extension by zero
  `ComplexShape.embeddingUpNat.extendFunctor E` to `ℤ`-graded complexes, then
  `forget` (the underlying tower), then `lim`. Its value at `K` is
  `K.adicLimit` (`adicLimitFunctor_obj`, by `rfl`).
- `adicLimitCohomologyFunctor E ℓ n`: `adicLimitFunctor` followed by `H^n`, so
  `K ↦ H^n(lim_m K_m)` (`adicLimitCohomologyFunctor_obj`).
- `levelCohomologyLimitFunctor E ℓ n`: `K ↦ lim_m H^n(K_m)`, the underlying
  tower followed by `H^n` levelwise and then `lim`. Its value at `K` is
  `K.levelCohomologyLimit n` (`levelCohomologyLimitFunctor_obj`).
- `adicLimitComparisonNatTrans E ℓ n`: the published comparisons
  `K.adicLimitComparison n : H^n(lim_m K_m) ⟶ lim_m H^n(K_m)` form a natural
  transformation from `adicLimitCohomologyFunctor` to
  `levelCohomologyLimitFunctor` (`adicLimitComparisonNatTrans_app`).
  Naturality is checked on the limit projections, using
  `adicLimitComparison_π`, `limMap_π` and the naturality of
  `extendHomologyNatIso`.

## Rational structures for modules

`R : Type u` and `S : Type uS` are commutative rings with an `R`-algebra
structure on `S`, and the systems consist of complexes in `ModuleCat.{v} R`.
The rational functors take values in `ModuleCat.{max v uS} S`, the category
in which Mathlib's `ModuleCat.extendScalars` takes its values.

- `rationalAdicLimitCohomology R S ℓ n`: `adicLimitCohomologyFunctor`
  followed by extension of scalars, `K ↦ S ⊗_R H^n(lim_m K_m)`.
- `rationalLevelCohomologyLimit R S ℓ n`: `K ↦ S ⊗_R lim_m H^n(K_m)`.
- `rationalAdicLimitComparison R S ℓ n`: the comparison
  `S ⊗_R H^n(lim_m K_m) ⟶ S ⊗_R lim_m H^n(K_m)`, the whiskering of
  `adicLimitComparisonNatTrans` by extension of scalars. By
  `rationalAdicLimitComparison_app` its component at `K` is the extension of
  scalars of `K.adicLimitComparison n`.
- `isIso_rationalAdicLimitComparison_app R S ℓ hS K hfin n`: given
  `hS : FiniteCohomologyInverseLimitStatement R` and finite cohomology of all
  levels of `K` in all degrees (`hfin`), this component is an isomorphism. The
  integral comparison is one by the published
  `isIso_adicLimitComparison_of_finite`, and functors preserve isomorphisms.
- `adicLimitCohomologyRationalUnit R S ℓ n` and
  `levelCohomologyLimitRationalUnit R S ℓ n`: the natural maps from the
  integral structures `H^n(lim_m K_m)` and `lim_m H^n(K_m)` to the
  restriction of scalars of the rational ones. Their components are the unit
  of Mathlib's adjunction `ModuleCat.extendRestrictScalarsAdj`, so
  `x ↦ 1 ⊗ x` (`adicLimitCohomologyRationalUnit_app_apply`,
  `levelCohomologyLimitRationalUnit_app_apply`). They are stated for systems
  of modules in `ModuleCat.{max v uS} R`, where the source and the
  restriction of scalars of the target lie in the same category.
- `adicLimitComparisonNatTrans_comp_rationalUnit R S ℓ n`: the integral
  comparison followed by the unit equals the unit followed by the restriction
  of scalars of the rational comparison. This is the naturality of the unit.

## Additivity of extension of scalars

- `moduleExtendScalars_additive φ` (instance): for commutative rings
  `R : Type u` and `S : Type uS` and any ring homomorphism `φ : R →+* S`,
  `ModuleCat.extendScalars φ` is additive, with modules in any universe `v`.
  It is checked on the generators `1 ⊗ m` (`ModuleCat.ExtendScalars.hom_ext`,
  `TensorProduct.tmul_add`). The Library has the same property for less
  general universes, `moduleExtendScalarsAdditive` (AdditiveAdjunction
  module, `R`, `S` and the modules in one universe) and
  `ModuleComplex.extendScalars_additive` (PerfectModuleComplexHomotopy
  module, `R` and `S` in one universe). Neither is imported here, and the
  universes needed here differ.

## Flat extension of scalars for modules

`R`, `S`, `ℓ` are as above.

- `moduleExtendScalars_map_exact R S T hT`: if `S` is flat over `R`
  (`[Module.Flat R S]`), extension of scalars sends an exact short complex `T`
  in `ModuleCat.{v} R` to an exact short complex. Proof: exactness of short
  complexes of modules is `range = ker`
  (`ShortComplex.moduleCat_exact_iff_range_eq_ker`, `LinearMap.exact_iff`),
  and tensoring with a flat module preserves it (`Module.Flat.lTensor_exact`).
  After unfolding, `S` appears as an `R`-algebra through
  `(algebraMap S S).comp (algebraMap R S)`, which is flat by
  `RingHom.flat_algebraMap_iff` and `Algebra.algebraMap_self`. This is the
  module counterpart of the published `repExtendScalars_map_exact`.
- `moduleExtendScalars_preservesHomology R S` (instance): hence, for `S` flat
  over `R`, extension of scalars preserves homology
  (`Functor.preservesHomology_of_map_exact`).
- `adicLimitBaseChangeHomologyIso R S ℓ n`: for `S` flat over `R`, the
  natural isomorphism `H^n(S ⊗_R lim_m K_m) ≅ S ⊗_R H^n(lim_m K_m)`, i.e.
  between `adicLimitFunctor` followed by the degreewise extension of scalars
  and `H^n`, and `rationalAdicLimitCohomology R S ℓ n`. It is the published
  `mapHomologicalComplexHomologyIso` for extension of scalars, whiskered by
  `adicLimitFunctor`. The complex `S ⊗_R lim_m K_m` is the extension of
  scalars of the limit, not the limit of the `S ⊗_R K_m`.
- `adicLimitBaseChangeLevelCohomologyIso R S ℓ hS K hfin n`: for `S` flat
  over `R`, given `hS` and `hfin` as in
  `isIso_rationalAdicLimitComparison_app`,
  `H^n(S ⊗_R lim_m K_m) ≅ S ⊗_R lim_m H^n(K_m)`: the component at `K` of
  `adicLimitBaseChangeHomologyIso` followed by the rational comparison.

## Rational structures for representations

`k : Type u` and `S : Type uS` are commutative rings with a `k`-algebra
structure on `S`, `G : Type w` is a monoid, and the systems consist of
complexes in `Rep.{v} k G`. The rational functors take values in
`Rep.{max uS v} S G`, where the published `repExtendScalars k S G` takes its
values. The declarations are the representation versions of the previous
two sections, with the same proofs:

- `repRationalAdicLimitCohomology k S G ℓ n` (`K ↦ S ⊗_k H^n(lim_m K_m)`),
  `repRationalLevelCohomologyLimit k S G ℓ n` (`K ↦ S ⊗_k lim_m H^n(K_m)`)
  and the comparison `repRationalAdicLimitComparison k S G ℓ n`, with
  `repRationalAdicLimitComparison_app`.
- `isIso_repRationalAdicLimitComparison_app k S G ℓ hS K hfin n`: given
  `hS : FiniteCohomologyInverseLimitStatement k` and finite level
  cohomology, the comparison is an isomorphism, by the published
  `isIso_adicLimitComparison_rep`.
- `repAdicLimitCohomologyRationalUnit k S G ℓ n` and
  `repLevelCohomologyLimitRationalUnit k S G ℓ n`: the maps `v ↦ 1 ⊗ v` to
  the restriction of scalars `repRestrictScalars k S G` of the rational
  structures, with components the published `repExtendScalarsUnit`, for
  systems in `Rep.{max uS v} k G`.
  `repAdicLimitComparisonNatTrans_comp_rationalUnit` is their compatibility
  with the comparisons.
- `repAdicLimitBaseChangeHomologyIso k S G ℓ n` (for `S` flat over `k`):
  `H^n(S ⊗_k lim_m K_m) ≅ S ⊗_k H^n(lim_m K_m)`, naturally in `K`, from the
  published instance `repExtendScalars_preservesHomology`.
- `repAdicLimitBaseChangeLevelCohomologyIso k S G ℓ hS K hfin n` (for `S`
  flat over `k`): `H^n(S ⊗_k lim_m K_m) ≅ S ⊗_k lim_m H^n(K_m)`.

## Smooth Godement towers: integral and rational structures

`R` is a commutative ring, `G` a topological group, `X` a topological space
with a `G`-action by homeomorphisms and `HasStableNeighbourhoods G X`, all in
one universe `u`. `T : SmoothSheafDivisibleSystem R G X ℓ`, and
`h : SmoothGodementZeroExactStatement R G X` is Worker 3's unproved
exactness statement for the degree-zero smooth Godement functor (an explicit
hypothesis). `F_m^•` is the smooth Godement resolution of the level `T_m`.
`Φ` is an additive sections functor on smooth sheaves that preserves finite
limits. `D : ℕ`, and `hterm`, `hres` are the surjectivity hypotheses of the
published truncated section complexes
`G_m^• = smoothGodementTruncatedSectionsSystem h T D Φ hterm hres`: `Φ` maps
the projections of the term systems in degrees `≤ D` and of the residual
system in degree `D + 1` to epimorphisms.

- `smoothGodementSectionsCohomologyLimit h T Φ n` (`abbrev`): the integral
  structure `lim_m H^n(Φ(F_m^•))`, the limit of the degree-`n` cohomologies of
  the published tower `smoothGodementSectionsTower h T Φ`, for `Φ` with
  values in any abelian category `E` with limits of shape `ℕᵒᵖ`.
- `smoothGodementRationalCohomology h T S Φ n` (`abbrev`): for `Φ` with
  values in `ModuleCat.{v'} R'` (a commutative ring `R' : Type u'`, and an
  `R'`-algebra `S : Type uS`), the rational structure
  `S ⊗_{R'} lim_m H^n(Φ(F_m^•))` in `ModuleCat.{max v' uS} S`.
- `smoothGodementRationalCohomologyUnit h T S Φ n`, for `Φ` with values in
  `ModuleCat.{max v' uS} R'`: the map `x ↦ 1 ⊗ x` from the integral to the
  restriction of scalars of the rational structure
  (`smoothGodementRationalCohomologyUnit_apply`).
- `smoothGodementRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn`: given
  `hS : FiniteCohomologyInverseLimitStatement R'` and finite cohomology of
  every level `G_m^•` (`hfin`), for `n ≤ D + 1`,
  `S ⊗_{R'} H^n(lim_m G_m^•) ≅ S ⊗_{R'} lim_m H^n(Φ(F_m^•))`. Its source is
  `rationalAdicLimitCohomology R' S ℓ n` at the system `G^•`. It is the
  extension of scalars of the published
  `smoothGodementTruncatedSectionsAdicLimitHomologyIso`.
- `smoothGodementTruncatedSectionsAdicLimitHomologyIso_hom_comp_rationalUnit`:
  for `Φ` with values in `ModuleCat.{max v' uS} R'`, the published integral
  isomorphism followed by `smoothGodementRationalCohomologyUnit` equals
  `adicLimitCohomologyRationalUnit` at `G^•` followed by the restriction of
  scalars of `smoothGodementRationalAdicLimitIso`. So the integral and
  rational isomorphisms are compatible with `x ↦ 1 ⊗ x`.
- `smoothGodementBaseChangeAdicLimitHomologyIso h T S D Φ hterm hres hS hfin
  hn`: for `S` flat over `R'` and `n ≤ D + 1`,
  `H^n(S ⊗_{R'} lim_m G_m^•) ≅ S ⊗_{R'} lim_m H^n(Φ(F_m^•))`, i.e. "tensor,
  then take cohomology" gives the rational structure. It is
  `adicLimitBaseChangeHomologyIso` at `G^•` followed by
  `smoothGodementRationalAdicLimitIso`.

The representation versions, for `Φ` with values in `Rep.{v'} k G'` (a
commutative ring `k : Type u'`, a `k`-algebra `S : Type uS` and a monoid
`G' : Type w`), use the published
`smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep` and
`repExtendScalars`:

- `smoothGodementRepRationalCohomology h T S Φ n` (`abbrev`):
  `S ⊗_k lim_m H^n(Φ(F_m^•))` in `Rep.{max uS v'} S G'`.
- `smoothGodementRepRationalCohomologyUnit h T S Φ n`: the map `v ↦ 1 ⊗ v`
  (published `repExtendScalarsUnit`), for `Φ` with values in
  `Rep.{max uS v'} k G'`.
- `smoothGodementRepRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn`
  (`n ≤ D + 1`): `S ⊗_k H^n(lim_m G_m^•) ≅ S ⊗_k lim_m H^n(Φ(F_m^•))`.
- `smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep_hom_comp_rationalUnit`:
  compatibility with `v ↦ 1 ⊗ v`, as above.
- `smoothGodementRepBaseChangeAdicLimitHomologyIso h T S D Φ hterm hres hS
  hfin hn` (for `S` flat over `k`, `n ≤ D + 1`):
  `H^n(S ⊗_k lim_m G_m^•) ≅ S ⊗_k lim_m H^n(Φ(F_m^•))`.

## Harris's Lemma 2.8 after a flat extension of scalars

`R`, `G`, `X`, `h`, `T` and `D` are as in the previous section, and
`hterm`, `hres` are the surjectivity hypotheses for the compact sections
functor `smoothSheafCompactSections R G X`. `K` is the published system
`smoothGodementTruncatedCompactSectionsSystem h T D hterm hres` of
compact-section complexes `C_m^• = Γ_c(G_m^•)`. `S : Type u` is a
commutative `R`-algebra in the universe of `R`, as required by the published
`quotientInvariantsInverseLimitBaseChange`. The remaining variables are those
of the published Lemma 2.8: a filtered preorder `ι : Type u`, an antitone
family `H` of normal subgroups of finite index, `hK` (the `H i`-invariants of
the projections of `K` are epimorphisms) and `hk` (the orders of the kernels
of the transitions `G ⧸ H j → G ⧸ H i` are units in `R`).

- `smoothGodementQuotientInvariantsInverseLimitBaseChange h T D hterm hres S H
  hH hK hk` (`abbrev`): Harris's "`(lim C_m^•)` tensored with `S`", the
  published `quotientInvariantsInverseLimitBaseChange` with `N = D + 2` for
  `K`, a `ℤ`-graded complex in `Rep.{u} S G`. By
  `smoothGodementQuotientInvariantsInverseLimitBaseChange_eq` (`rfl`) it is the
  degreewise extension of scalars `repExtendScalarsComplex R S G` of the
  published `smoothGodementQuotientInvariantsInverseLimit`.
- `smoothGodementQuotientInvariantsInverseLimitBaseChangeHomologyIso … hS hS'
  hP hR htriv hfin hn`: for `S` flat over `R` and `n ≤ D + 1`,
  `H^n((lim C_m^•) ⊗ S) ≅ S ⊗_R lim_m H^n(Γ_c(F_m^•))` as representations of
  `G` over `S`, where the right side is `repExtendScalars R S G` of the limit
  of the degree-`n` cohomologies of `smoothGodementCompactSectionsRepTower`.
  The hypotheses are those of the published
  `smoothGodementQuotientInvariantsInverseLimitHomologyIso`:
  `hS : ProPInvariantSubcomplexStatement`,
  `hS' : FiniteCohomologyInverseLimitStatement R`, every `H i` pro-`p`
  (`hP`) with `p` a unit in `R` (`hR`), trivial action of the `H i` on the
  cohomology of the levels of `K` (`htriv`), and finiteness of that
  cohomology (`hfin`). Proof: `mapHomologicalComplexHomologyIso` for
  `repExtendScalars` (which preserves homology since `S` is flat), then the
  extension of scalars of the published integral isomorphism.

## `ℓ`-adic and rational `ℓ`-adic coefficients

`ℓ` is a prime (`[Fact ℓ.Prime]`), `ℤ_[ℓ]` and `ℚ_[ℓ]` are Mathlib's
`ℓ`-adic integers and numbers, and `G`, `X` are in `Type`.

- `padicInt_flat_padic ℓ` (instance): `ℚ_[ℓ]` is flat over `ℤ_[ℓ]`. It is
  the localization of `ℤ_[ℓ]` at its non-zero-divisors (Mathlib's instance
  `PadicInt.isFractionRing`), and localizations are flat
  (`IsLocalization.flat`).

In the rest, `h : SmoothGodementZeroExactStatement ℤ_[ℓ] G X` and the system
is the published constant system
`constantSheafSystem (padicInt_isSMulRegular ℓ) G X` of the locally constant
sheaves of the trivial representations `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]`.

- `padicConstantGodementRationalCohomology ℓ G X h Φ n` (`abbrev`): for `Φ`
  with values in `ModuleCat.{v'} ℤ_[ℓ]`, the rational structure
  `ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Φ(F_m^•))`, i.e. `smoothGodementRationalCohomology`
  with `S = ℚ_[ℓ]`.
- `padicConstantGodementBaseChangeAdicLimitHomologyIso ℓ G X h D Φ hterm hres
  hS hfin hn`: for `n ≤ D + 1`, with `hS` and `hfin` as in
  `smoothGodementBaseChangeAdicLimitHomologyIso`,
  `H^n(ℚ_ℓ ⊗_{ℤ_ℓ} lim_m G_m^•) ≅ ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Φ(F_m^•))`, where
  `lim_m G_m^•` is the published `constantGodementAdicSectionsComplex`.
- `padicConstantQuotientInvariantsInverseLimitRational ℓ G X h D hterm hres H
  hH hK hk` (`abbrev`): Harris's `(lim C_m^•) ⊗_{ℤ_ℓ} ℚ_ℓ`, a complex in
  `Rep.{0} ℚ_[ℓ] G`, for a filtered preorder `ι : Type` and `hk` assuming only
  that the orders of the transition kernels are prime to `ℓ` (they are then
  units in `ℤ_[ℓ]` by the published `padicInt_isUnit_natCast`). By
  `padicConstantQuotientInvariantsInverseLimitRational_eq` (`rfl`) it is the
  degreewise extension of scalars along `ℤ_[ℓ] → ℚ_[ℓ]` of the published
  `padicConstantQuotientInvariantsInverseLimit`.
- `padicConstantQuotientInvariantsInverseLimitRationalHomologyIso … hS hS'
  hP hpℓ htriv hfin hn`: Harris's Lemma 2.8 with `ℚ_ℓ` coefficients in
  degrees `n ≤ D + 1`:
  `H^n((lim C_m^•) ⊗_{ℤ_ℓ} ℚ_ℓ) ≅ ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Γ_c(F_m^•))`, where
  `F_m^•` is the smooth Godement resolution of the constant sheaf of
  `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]`. The hypotheses are those of
  `smoothGodementQuotientInvariantsInverseLimitBaseChangeHomologyIso`, except
  that `hR` is replaced by `hpℓ : ℓ.Coprime p`.

## Provenance and interpretation

1. Harris, *Supercuspidal representations in the cohomology of Drinfel'd
   upper half spaces; elaboration of Carayol's program*, Invent. Math. 129
   (1997), printed p.92 (one-based PDF page 18): "Berkovich shows that the
   discrete complexes calculating cohomology with coefficients in Z/ℓ^nZ, as
   n varies, satisfy an appropriate Mittag-Leffler condition, and give rise
   in the inverse limit over n to a complex of smooth Z_ℓ[S(e,d)]-modules,
   whose cohomology equals H_c^•(U(e,N), Z_ℓ). [...] Tensoring with Q_ℓ, we
   obtain our complex C(e,d)." Worker 61 read this passage in the original
   for the published ScalarExtension module.
2. Deligne, *Cohomologie étale* (SGA 4½), Lecture Notes in Mathematics 569
   (1977), *Rapport sur la formule des traces*, 2.10, printed p.84 (one-based
   PDF page 89): for a constructible `ℚ_ℓ`-sheaf `𝔉 ∼ 𝔉' ⊗ ℚ_ℓ`, the group
   "`(lim H^q_c(X, 𝔉' ⊗ ℤ/ℓ^n)) ⊗_{ℤ_ℓ} ℚ_ℓ` [...] se note `H^q_c(X, 𝔉)`".
   The full quotation is in the published EtaleRationalCohomology module.
3. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
   J. Math. Kyoto Univ. 39-2 (1999), Lemma 2.8, printed p.306 (one-based PDF
   page 8): "For every q, there is a canonical isomorphism
   H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)." The quotations
   from pp.305–306 on `G_m^•`, (2.3) and the pro-`p` subgroups are in the
   published ConstantInverseLimit module. These pages contain no tensor
   product with `ℚ_ℓ`.

Our rendering:

1. Integral and rational structures. The integral structure is
   `lim_m H^n(Φ(F_m^•))`, as in the published ConstantInverseLimit module.
   With compact sections and the constant system it stands for
   `lim_m H_c^n(U, ℤ / ℓ^m ℤ)`, the integral `ℓ`-adic cohomology (Harris
   1997's `H_c^•(U(e,N), ℤ_ℓ)`); this reading is an interpretation. Its
   rational structure is its extension of scalars `S ⊗_R lim_m H^n`, the
   recipe of SGA 4½ 2.10 ("inverse limit of the torsion cohomology, then
   `⊗_{ℤ_ℓ} ℚ_ℓ`"). `x ↦ 1 ⊗ x` is the natural map between them.
2. Harris's order of operations. Harris takes the inverse limit of the
   complexes, tensors the complex with `ℚ_ℓ`, and then takes cohomology. The
   published ScalarExtension module defines the tensored complex
   `quotientInvariantsInverseLimitBaseChange` but states that it proves no
   comparison: "we do not prove that extension of scalars commutes with the
   inverse limit or with cohomology". This module proves the comparison with
   cohomology for flat algebras, such as `ℤ_[ℓ] → ℚ_[ℓ]`: "cohomology, then
   tensor" and "tensor, then cohomology" agree
   (`adicLimitBaseChangeHomologyIso` and its representation version). With
   the published Lemma 2.8 this identifies the cohomology of Harris's
   tensored complex with `S ⊗ lim_m H^n(Γ_c(F_m^•))`, the SGA 4½ recipe, in
   degrees `≤ D + 1`. It still does not prove that extension of scalars
   commutes with the inverse limit of the complexes; it is not needed for
   these statements.
3. Coefficients. Harris's `ℤ_ℓ → ℚ_ℓ` is Mathlib's `ℤ_[ℓ] → ℚ_[ℓ]`, and
   Harris's levels `ℤ / ℓ^m ℤ` are the rings `ℤ_[ℓ] / ℓ^m ℤ_[ℓ]`, as in the
   published ConstantInverseLimit module (`padicLevelRingEquiv`). The
   general statements allow any (flat) commutative algebra `S`, as the
   published ScalarExtension module does.
4. Derived content. The functors, natural transformations, flatness
   arguments and the compatibilities with `x ↦ 1 ⊗ x` are ours. They are
   standard: extension of scalars along a flat algebra is exact, hence
   commutes with cohomology. The degree bound `n ≤ D + 1` comes from the
   truncations of the published ConstantTruncation and ConstantInverseLimit
   modules.
5. What stays a hypothesis. `SmoothGodementZeroExactStatement` (`h`); the
   surjectivity of the sections functors on the projections (`hterm`,
   `hres`) and of the `H i`-invariants (`hK`); the inverse-limit and pro-`p`
   statements (`hS`, `hS'`); the unit or coprimality hypotheses on `p` and on
   the transition kernels (`hR`, `hpℓ`, `hk`); and the finiteness and trivial
   action of the level cohomology (`hfin`, `htriv`). Reading `G` as Harris's
   `S(e,d)` or `S(ẽ)` and `X` as `U(e,N)` or `U(ẽ)` is our interpretation,
   as in the parent modules; the Library's sheaves are equivariant sheaves
   on topological spaces, not étale sheaves on rigid analytic spaces.

## Scope

The module constructs the functors and comparison maps above and proves the
flat base-change isomorphisms. It does not prove that the limits or their
extensions of scalars are smooth representations, that the rational
cohomology is finite dimensional, or any identification with étale
cohomology with `ℤ_ℓ` or `ℚ_ℓ` coefficients. Harris 1999's `ℓ`-adic sheaf
`W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` and its cohomology are not formalized here, and no
statement is made about degrees above `D + 1`.

Source registration: Harris 1997, `harris-1997-drinfeld-cohomology`, SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
SGA 4½, `deligne-1977-sga4-half-cohomologie-etale`, SHA-256
`fb2939521f4c0ea0cdd55a90bec2e618e32fb433c78b194e705c6d989f4e42a6`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
