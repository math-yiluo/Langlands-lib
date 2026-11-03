# Truncated constant Godement systems and their section complexes

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem.Truncation` (Worker 61): the generic
  truncation `truncation S d sq D Z p ι hpι` of a system of complexes given
  degree by degree, with terms `truncationTerm`, the identifications
  `truncationTerm_of_le` and `truncationTerm_of_eq`, the differentials
  `truncationDifferential`, the degree isomorphisms `truncationDegreeIsoOfLE`
  and the inclusion `truncationHom` with components `truncationInclusion`.
  Its smooth case is `smoothGodementTruncatedResolutionSystem h T D` with
  inclusion `smoothGodementTruncatedResolutionHom h T D` into the system
  `smoothGodementResolutionSystem h T`, and `truncatedResolutionSystem_obj_exactAt`
  and `isZero_truncatedResolutionSystem_obj_X` state exactness in positive
  degrees and vanishing above `D + 1`.
- `Langlands.Cohomology.DivisibleSystem.Coaugmented` (Worker 61): for a system
  `T` and a coaugmented functor `η : 𝟭 C ⟶ F`, the residual systems
  `T.residualSystem F η q`, the term systems `T.termSystem F η q`, the residual
  quotients and inclusions, the differentials `termDifferential`, and the level
  isomorphisms `residualSystemObjIso` and `termSystemObjIso` with the cokernel
  construction at `T m`. In the smooth case these are
  `smoothGodementResidualSystem h T q`, `smoothGodementTermSystem h T q`,
  `smoothGodementTermSystemObjIso` and `smoothGodementCoaugmentation h T`
  (Harris's `b : T ⟶ F^0`).
- `Langlands.Cohomology.DivisibleSystem.Resolution` (Worker 61):
  `smoothGodementResolutionSystem h T` and its level isomorphisms
  `smoothGodementResolutionSystemObjIso h T m` with the smooth Godement complex
  `smoothComplex R G X (T m)`.
- `Langlands.Cohomology.DivisibleSystem.Sections` (Worker 61):
  `truncatedResolutionSectionsSystem`, `resolutionSectionsSystem` and
  `truncatedResolutionSectionsHom` (a sections functor `Φ` applied degreewise),
  and their compact cases `smoothGodementTruncatedCompactSectionsSystem` and
  `smoothGodementTruncatedInvariantCompactSectionsSystem`.
- `Langlands.Cohomology.DivisibleSystem.Invariants` (Worker 61):
  `smoothQuotientInvariants R H : SmoothRep R G ⥤ Rep R (G ⧸ H)` for a normal
  subgroup `H` and `smoothGodementTruncatedQuotientInvariantSectionsSystem`.
- `Langlands.Cohomology.DivisibleSystem.ConstantCoefficients` (Worker 61): the
  constant sheaf system `constantSheafSystem hℓ G X` of the locally constant
  sheaves of the trivial smooth representations `R / ℓ ^ m R`, its level
  isomorphisms `constantSheafSystemObjIso`, `constantGodementResolutionSystem`
  and `constantGodementResolutionSystemObjIso`, and the `ℤ` versions
  `intConstantSheafSystem ℓ hℓ G X` and `intConstantSheafSystemObjIso` with
  levels `ZMod (ℓ ^ m)`.
- Through them: Worker 13's cokernel construction
  `Langlands.Cohomology.CokernelComplex` (`residual`, `quotient`, `inclusion`),
  and the smooth Godement functor `smoothZeroFunctor R G X`, its
  coaugmentation `smoothCoaugmentation R G X`, `smoothComplexFunctor R G X` and
  `smoothComplex R G X F` (`Langlands.Sheaf.Equivariant.Godement.Smooth`).
  `smoothComplex R G X F` is the cokernel construction applied to `F`: its
  degree-`q` term is `smoothZeroFunctor` of `residual q` at `F`, and its
  differential is `quotient q` followed by `inclusion (q + 1)`.

All names below are in the namespace `Langlands.Cohomology.DivisibleSystem`.
Write `T m` for `T.obj m`, `F^q` for the smooth Godement term systems and
`R^q` for the residual objects `CokernelComplex.residual … q` (not to be
confused with the ring `R`). `R`, the groups and the spaces lie in one universe
`u`, as in the parent modules; the `ℤ` cases use `Type`.

The exactness of the degree-zero smooth Godement functor is Worker 3's
unproved proposition `SmoothGodementZeroExactStatement R G X`. Every smooth
declaration below takes a proof `h` of it as an explicit argument.

## Levels of the generic truncation

`C` is an abelian category, and `S`, `d`, `sq`, `D`, `Z`, `p`, `ι`, `hpι` and
`hιd` are as in the Truncation module.

- `truncation_obj_X_of_le` and `truncation_obj_X_top`: in degree `q ≤ D` the
  level-`m` term of `truncation …` equals `(S q) m`, and in degree `D + 1` it
  equals `Z m`. These are the level-`m` objects of `truncationTerm_of_le` and
  `truncationTerm_of_eq`.
- `truncation_obj_d_comp_eqToHom_of_lt` and
  `truncation_obj_d_comp_eqToHom_top`: under these equalities the level-`m`
  differential in degree `q < D` is the component of `d q`, and in degree `D`
  it is the component of `p`.
- `truncationDegreeIsoOfLE_inv_tower_app`: the components of the inverse of
  `truncationDegreeIsoOfLE` are these equalities.
- `truncationHom_tower_app_f_of_le` and `truncationHom_tower_app_f_top`: the
  level-`m` component of `truncationHom` is the identification in degrees
  `q ≤ D` and the component of `ι` in degree `D + 1`.

## The truncated smooth Godement resolutions

`R` is a commutative ring, `G` a topological group, `X` a topological space
with a `G`-action by homeomorphisms and `HasStableNeighbourhoods G X`,
`T : SmoothSheafDivisibleSystem R G X ℓ` and `D : ℕ`.

- `isZero_smoothGodementTruncatedResolutionSystem_obj_X` and
  `smoothGodementTruncatedResolutionSystem_obj_exactAt`: every level of
  `smoothGodementTruncatedResolutionSystem h T D` is zero in degrees `> D + 1`
  and exact in every positive degree (the Truncation module's statements,
  with the instances supplied by `h`).
- `smoothGodementTruncatedResolutionSystem_obj_X_of_le` and
  `smoothGodementTruncatedResolutionSystem_obj_X_top`: the level-`m` term is
  `(F^q) m` in degree `q ≤ D` and `(smoothGodementResidualSystem h T (D + 1)) m`
  in degree `D + 1`.
- `smoothGodementTruncatedObjXIso h T D m hq`, for `q ≤ D`, is the isomorphism
  from the level-`m` term in degree `q` to `(smoothComplex R G X (T m)).X q`:
  the equality above followed by `smoothGodementTermSystemObjIso`.
- `smoothGodementResidualSystemObjIso h T q m` is the Coaugmented module's
  `residualSystemObjIso` in the smooth case: level `m` of the residual system
  is `R^q` at `T m`. `smoothGodementTruncatedObjXIsoTop h T D m` identifies the
  degree-`(D + 1)` term with `R^(D + 1)` at `T m`.
- `smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom`: for
  `q < D`, these isomorphisms carry the level-`m` differential to the
  differential of `smoothComplex R G X (T m)`.
  `smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom`: in
  degree `D`, they carry it to the cokernel projection
  `CokernelComplex.quotient … D : F^D ⟶ R^(D + 1)` at `T m`.
- `smoothGodementTruncatedResolutionHom_f_comp_objIso_hom_f`: composed with
  `smoothGodementResolutionSystemObjIso h T m`, the level-`m` component of the
  inclusion `smoothGodementTruncatedResolutionHom h T D` is
  `smoothGodementTruncatedObjXIso` in degrees `q ≤ D`, so it is the identity
  under the level isomorphisms.
  `smoothGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f`: in degree
  `D + 1` it is the coaugmentation `CokernelComplex.inclusion … (D + 1) :
  R^(D + 1) ⟶ F^(D + 1)` at `T m`.
- `smoothGodementTruncatedDegreeIsoOfLE h T D hq` is `truncationDegreeIsoOfLE`
  in the smooth case: for `q ≤ D` the degree-`q` system of the truncated system
  is `smoothGodementTermSystem h T q`.
  `smoothGodementTruncatedDegreeIsoOfLE_inv_tower_app` gives its inverse
  components.
- `smoothGodementTruncatedCoaugmentation h T D :
  T ⟶ (smoothGodementTruncatedResolutionSystem h T D).degree 0` is
  `smoothGodementCoaugmentation h T` followed by the inverse of
  `smoothGodementTruncatedDegreeIsoOfLE` in degree zero.
  `smoothGodementTruncatedCoaugmentation_tower_app_comp_objXIso_hom`: under
  `smoothGodementTruncatedObjXIso` in degree zero its level-`m` component is
  the level-`m` component of `smoothGodementCoaugmentation h T` followed by
  `smoothGodementTermSystemObjIso h T 0 m`.

## Section complexes for a sections functor

`E` is an abelian category and `Φ : SmoothTopologicalSheaf R G X ⥤ E` is
additive and preserves finite limits. As in the Sections module, `hterm` says
that `Φ` maps the projections of `F^q`, `q ≤ D`, to epimorphisms, `hres` says
the same for `smoothGodementResidualSystem h T (D + 1)`, and `hall` for every
`F^q`. These hypotheses are explicit arguments.

- `smoothGodementTruncatedSectionsSystem h T D Φ hterm hres` is the Sections
  module's `truncatedResolutionSectionsSystem` for the smooth Godement
  functor: Harris's system `{G_m^•(U)}` with `Φ` in place of sections over `U`.
  `smoothGodementSectionsSystem h T Φ hall` is `resolutionSectionsSystem`, and
  `smoothGodementTruncatedSectionsHom h T D Φ hall hres` is
  `truncatedResolutionSectionsHom`, `Φ` applied to the inclusion.
- `smoothGodementTruncatedCompactSectionsSystem_eq`,
  `smoothGodementTruncatedInvariantCompactSectionsSystem_eq` and
  `smoothGodementTruncatedQuotientInvariantSectionsSystem_eq`: the published
  compact-section system, invariant compact-section system and
  `H`-quotient-invariant system are `smoothGodementTruncatedSectionsSystem` for
  `Φ = smoothSheafCompactSections R G X`,
  `Φ = SmoothSheafCohomology.invariantCompactSections R G X` and
  `Φ = smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H`. All
  three hold by `rfl`, so the statements below apply to them.
- `isZero_smoothGodementTruncatedSectionsSystem_obj_X`: every level is zero
  in degrees `> D + 1`.
- `smoothGodementTruncatedSectionsObjXIso` and
  `smoothGodementTruncatedSectionsObjXIsoTop` are the images under `Φ` of
  `smoothGodementTruncatedObjXIso` and `smoothGodementTruncatedObjXIsoTop`.
  `smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIso_hom` and
  `smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTop_hom`: under
  them the differentials are `Φ` of the differentials of
  `smoothComplex R G X (T m)` in degrees `q < D` and `Φ` of the cokernel
  projection in degree `D`.
- `smoothGodementSectionsObjIso h T Φ hall m`: level `m` of the full section
  complexes is `Φ.mapHomologicalComplex` of `smoothComplex R G X (T m)`.
  `smoothGodementTruncatedSectionsHom_f_comp_objIso_hom_f` and
  `smoothGodementTruncatedSectionsHom_f_top_comp_objIso_hom_f`: the inclusion
  is the identity in degrees `q ≤ D` and `Φ` of the coaugmentation
  `R^(D + 1) ⟶ F^(D + 1)` in degree `D + 1`.

The proofs apply `Φ.map_comp` to the statements of the previous section.

## Transport along a level isomorphism

For `m : ℕ` and an isomorphism `e : T m ≅ F` of smooth sheaves, the
declarations ending in `OfIso` compose the level isomorphisms above with the
images of `e` under `smoothComplexFunctor R G X` (degreewise, through
`HomologicalComplex.Hom.isoApp`) and under `CokernelComplex.residual … (D + 1)`.
They identify the level-`m` terms, differentials and inclusion components with
those of `smoothComplex R G X F` and of `R^(D + 1)` at `F`:
`smoothGodementTruncatedObjXIsoOfIso`, `smoothGodementTruncatedObjXIsoTopOfIso`,
`smoothGodementResolutionSystemObjIsoOfIso`, and the lemmas
`smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoOfIso_hom`,
`smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTopOfIso_hom`,
`smoothGodementTruncatedResolutionHom_f_comp_objIsoOfIso_hom_f` and
`smoothGodementTruncatedResolutionHom_f_top_comp_objIsoOfIso_hom_f`. The
section versions are `smoothGodementTruncatedSectionsObjXIsoOfIso`,
`smoothGodementTruncatedSectionsObjXIsoTopOfIso`,
`smoothGodementSectionsObjIsoOfIso` and the four lemmas
`smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoOfIso_hom`,
`smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTopOfIso_hom`,
`smoothGodementTruncatedSectionsHom_f_comp_objIsoOfIso_hom_f` and
`smoothGodementTruncatedSectionsHom_f_top_comp_objIsoOfIso_hom_f`. The differential and inclusion statements follow
because `smoothComplexFunctor R G X` maps `e` to a chain map and
`CokernelComplex.quotient` and `CokernelComplex.inclusion` are natural.

## The constant system

`ℓ : ℕ` and `hℓ : IsSMulRegular R (ℓ : R)`, as in the ConstantCoefficients
module.

- `constantLevelSheaf R ℓ G X m` (an `abbrev`) is the locally constant sheaf
  `(LocallyConstantSheaf.smoothFunctor R G X).obj` of the trivial smooth
  representation `R / ℓ ^ m R`: the target of `constantSheafSystemObjIso`.
- `constantGodementResolutionSystemObjIso_eq`: the published
  `constantGodementResolutionSystemObjIso hℓ G X h m` is
  `smoothGodementResolutionSystemObjIsoOfIso` along `constantSheafSystemObjIso`
  (`rfl`).
- `constantGodementTruncatedResolutionSystem hℓ G X h D`,
  `constantGodementTruncatedResolutionHom` and
  `constantGodementTruncatedCoaugmentation` (`abbrev`s) are the truncated
  system, its inclusion into `constantGodementResolutionSystem hℓ G X h` and
  `b`, for `T = constantSheafSystem hℓ G X`.
- `constantGodementTruncatedObjXIso` and `constantGodementTruncatedObjXIsoTop`
  identify the level-`m` terms with those of the smooth Godement complex of
  `constantLevelSheaf R ℓ G X m` in degrees `≤ D` and with `R^(D + 1)` at it in
  degree `D + 1`. The four lemmas
  `constantGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom`,
  `constantGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom`,
  `constantGodementTruncatedResolutionHom_f_comp_objIso_hom_f` and
  `constantGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f` describe the differentials and the inclusion
  as in the general case. They are the `OfIso` declarations along
  `constantSheafSystemObjIso`.
- `constantGodementTruncatedCompactSectionsSystem`,
  `constantGodementTruncatedInvariantCompactSectionsSystem` and
  `constantGodementTruncatedQuotientInvariantSectionsSystem` (`abbrev`s) are the
  published compact, invariant compact and `H`-quotient-invariant section
  systems of the truncated constant system, with values in complexes of
  `SmoothRep R G`, `ModuleCat R` and `Rep R (G ⧸ H)`.
- For a general `Φ`: `constantGodementTruncatedSectionsSystem`,
  `constantGodementSectionsSystem` and `constantGodementTruncatedSectionsHom`
  (`abbrev`s), the level isomorphisms
  `constantGodementTruncatedSectionsObjXIso`,
  `constantGodementTruncatedSectionsObjXIsoTop` and
  `constantGodementSectionsObjIso`, and the four lemmas on differentials and
  inclusion components
  `constantGodementTruncatedSectionsSystem_obj_d_comp_objXIso_hom`,
  `constantGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTop_hom`,
  `constantGodementTruncatedSectionsHom_f_comp_objIso_hom_f` and
  `constantGodementTruncatedSectionsHom_f_top_comp_objIso_hom_f`. By the `rfl` lemmas of the section on section complexes, they apply to the
  three published section systems.

## Integer coefficients

`G` and `X` lie in `Type`, `ℓ : ℕ` and `hℓ : ℓ ≠ 0`.

- `intConstantGodementTruncatedResolutionSystem ℓ hℓ G X h D` (an `abbrev`)
  is the truncated system for `intConstantSheafSystem ℓ hℓ G X`.
- `intConstantGodementTruncatedObjXIso` and
  `intConstantGodementTruncatedObjXIsoTop` identify its level-`m` terms with
  those of the smooth Godement complex of the locally constant sheaf of the
  trivial smooth representation `ZMod (ℓ ^ m)`, and with `R^(D + 1)` at that
  sheaf. They are the `OfIso` isomorphisms along
  `intConstantSheafSystemObjIso`.
- `intConstantGodementTruncatedSectionsSystem` (an `abbrev`) and
  `intConstantGodementTruncatedSectionsObjXIso`,
  `intConstantGodementTruncatedSectionsObjXIsoTop` do the same for the section
  complexes of a sections functor `Φ`.

The differential and inclusion statements for `ℤ` are those of the general
`OfIso` lemmas along `intConstantSheafSystemObjIso`; the module does not
restate them.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.304–305 (one-based
PDF pages 6–7). The quotations are those already used by the published
ConstantCoefficients, Truncation and Sections modules; Worker 61 read the
pages in the scanned original.

1. What Harris uses. Lemma 2.2 (p.304) resolves the constant sheaves
   `ℤ/ℓ^mℤ` by `ℓ`-divisible systems `{F_m^q}`. On p.305 he sets
   `G_m^• = τ_{≤D+1}(F_m^•)` and states Lemma 2.2 bis: for each `m` the
   constant sheaf `ℤ/ℓ^mℤ` has an `RΓ_c`-acyclic resolution of finite length
   `0 → ℤ/ℓ^mℤ → G_m^0 → ⋯ → G_m^{D+1} → 0` such that each `{G_m^q}` is an
   `ℓ`-divisible system. He then uses the section complexes `G_m^•(U(ẽ)_F̄)`
   and, after invariants under an open normal pro-`p` subgroup `H ⊂ S(ẽ)`,
   calls the family "an ℓ-divisible system of finite-length complexes [...],
   in the obvious sense".
2. What is formalized. The published modules construct these systems for any
   system `T` of smooth sheaves and leave the constant sheaves to a separate
   construction. This module applies them to the published constant system:
   `intConstantGodementTruncatedResolutionSystem ℓ hℓ G X h D` is the system
   `{G_m^•}` of Lemma 2.2 bis for the constant sheaves `ℤ/ℓ^mℤ` on a
   topological `G`-space, with `G_m^q` the smooth Godement terms for `q ≤ D`
   and the residual object `R^(D + 1)` in degree `D + 1`. As the Truncation
   module explains, that object is Harris's kernel of `F_m^{D+1} → F_m^{D+2}`
   (the LeftExact module's `residualInclusionIsKernel`).
   `constantGodementTruncatedCoaugmentation` is the map `ℤ/ℓ^mℤ → G_m^0`
   (for `R = ℤ`). The section systems are Harris's
   `{G_m^•(U)}` and `{G_m^•(U)^H}` with the published sections functors in
   place of sections over `U(ẽ)_F̄`. The level isomorphisms of this module
   make the terms, differentials, inclusion and coaugmentation explicit at
   each `m`; they are derived, not taken from Harris.
3. What stays a hypothesis. The exactness of the degree-zero smooth Godement
   functor (Harris's Fact 3 in this setting) is
   `SmoothGodementZeroExactStatement R G X`. The surjectivity of the sections
   functor on the projections (`hterm`, `hres`, `hall`) is not derived; Harris
   derives the case of `G_m^{D+1}` from Fact 2 and the snake lemma. The
   `RΓ_c`-acyclicity of the `G_m^q` and the exactness of
   `0 → ℤ/ℓ^mℤ → G_m^0 → G_m^1` are not stated here. Harris's `D` is the bound
   of Fact 2; here `D` is arbitrary.
4. Interpretation. Reading `G` as `S(ẽ)` and `X` as `U(ẽ)` is our
   interpretation, as in the parent modules. The Library's sheaves are
   equivariant sheaves on topological spaces with ordinary opens, not étale
   sheaves on rigid analytic spaces. The general `R` with `ℓ` a
   non-zero-divisor, the general sections functor `Φ`, the generic level
   lemmas and the `OfIso` transport are internal framework.

## Scope

The module proves no cohomology, acyclicity or surjectivity statement. Apart
from vanishing above `D + 1` and exactness in positive degrees of the sheaf
complexes, which come from the Truncation module, it only identifies terms
and maps. It does not construct `ℓ`-adic or `ℤ_ℓ`-coefficient limits, the
isomorphism (2.3), the free resolutions (2.4)–(2.5) or the complexes `C_m^•`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
