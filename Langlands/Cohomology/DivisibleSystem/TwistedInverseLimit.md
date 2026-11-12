# Harris's complexes `C^•_m`, (2.6), (2.7) and Lemma 2.8 on a twisted site

Author: Worker 26. Builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem.TwistedTruncation` (Worker 26). It provides the
  truncated discrete Godement system `G^•` of an `ℓ`-divisible system `T` of discrete
  sheaves on a twisted site, and the `ℓ`-divisible system
  `discreteGodementTruncatedCompactSectionsSystem` of finite-length complexes
  `Γ_c(G^•_m)` of smooth representations. Its isomorphism
  `discreteGodementTruncatedCompactHomologyIso` is Harris's (2.3).
- `Langlands.Cohomology.DivisibleSystem.AcyclicTruncation` (Worker 26). It provides the
  generic truncation, the augmentations `resolutionSystemAugmentation` and
  `truncatedResolutionAugmentation`, and `acyclicTruncatedSectionsHomologyIso`.
- Worker 61's generic `DivisibleSystem` modules, through
  `Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit`:
  - `InvariantLimit`: `quotientInvariantsLimit`, `quotientInvariantsLimitToRepExtend`,
    `quasiIso_quotientInvariantsLimitToRepExtend`;
  - `InverseLimit`: `quotientInvariantsInverseLimit`,
    `quotientInvariantsInverseLimitComparison`,
    `isIso_quotientInvariantsInverseLimitComparison`,
    `mapHomologicalComplexHomologyIso`, `finite_of_rep_iso`;
  - `ConstantInverseLimit`: `extendHomologyNatIso`, `extendLevelCohomologyLimitIso`;
  - `InvariantComparison`: `Rep.ρ_eq_id_of_iso`.
- Worker 3's statements `ProPInvariantSubcomplexStatement`
  (`Langlands.Cohomology.ProPInvariants.Statement`) and
  `FiniteCohomologyInverseLimitStatement` (`Langlands.Cohomology.InverseLimit.Statement`).
  Neither statement is proved in the Library. Both appear here only as hypotheses `hS` and
  `hS'`.
- The Library's `AcyclicResolution.resolutionComparison_naturality`
  (`Langlands.Cohomology.AcyclicResolution.Comparison`).

All names are in the namespace `Langlands.Cohomology.DivisibleSystem`.

## Purpose

Harris passes from the finite-length complexes `G^•_m(U(ẽ)_F̄)` of (2.3) to complexes
`C^•_m`, compares them by (2.6), deduces (2.7) and proves Lemma 2.8 for the inverse limit over
`m`. Worker 61 built these constructions for an arbitrary `ℓ`-divisible system `K` of
complexes of smooth representations. This module applies them to the twisted-site system
`K = Γ_c(G^•)` of `TwistedTruncation`. Through (2.3) it identifies the resulting cohomology
with the compactly supported cohomology `H^n_c(T m) = discreteCompactDerived n (T m)`.

The limit over `m` in Lemma 2.8 is a limit of functors of `m`. So this module first proves
that the isomorphisms (2.3) are natural in `m`. That proof is generic.

## Naturality of (2.3) (generic)

The setting is that of `AcyclicTruncation`: an abelian category `C`, an exact endofunctor `F`
with a monic coaugmentation `η : 𝟭 ⟶ F`, an `ℓ`-divisible system `T` and a bound `D`. For the
acyclic part, `C` has enough injectives, `Φ : C ⥤ E` is additive and left exact, every `F(M)`
is `Φ`-acyclic (`hF`), and `Rⁿ Φ(T m) = 0` for `n > D` (`hT`).

- `resolutionSystemAugmentation_naturality F η T f`: for `f : op m ⟶ op m'` in `ℕᵒᵖ`, the
  augmentations `T m ⟶ F^•_m` commute with the transition maps of `T` and of the resolution
  system. A map out of a complex concentrated in degree `0` is determined by its degree-`0`
  component (Mathlib's `HomologicalComplex.from_single_hom_ext`). In degree `0` the
  augmentation is the coaugmentation `T ⟶ F^0`, which is a morphism of systems.
- `truncatedResolutionAugmentation_naturality F η T D f`: the same for the augmentations
  `T m ⟶ G^•_m` of the truncation. In degree `0` the inclusion `G^• ⟶ F^•` is an isomorphism.
  It is cancelled on the right, and the inclusion is a morphism of systems. This reduces the
  claim to the previous lemma.
- `acyclicTruncatedSectionsHomologyNatIso Φ F η T D hF hT n`: the natural isomorphism, of
  functors `ℕᵒᵖ ⥤ E`, from `m ↦ Hⁿ(Φ(G^•_m))` to `m ↦ Rⁿ Φ(T m)`. Its components are
  `acyclicTruncatedSectionsHomologyIso` (`acyclicTruncatedSectionsHomologyNatIso_app`).
  Naturality is the Library's `AcyclicResolution.resolutionComparison_naturality` for the
  augmentations, applied with the previous lemma.

## The twisted site

The data are those of the `Compact` section of `TwistedTruncation`. They include `ρ`, `J`,
`L`, the Godement points `points` with `hpoints`, `R`, `T`, `D`, the compact-support points
`Ψ` with `E : PointEquivariance ρ Ψ`, and the hypotheses `hF` and `hT`. There is one
difference. Worker 61's constructions take complexes of `SmoothRep.{uR, uG, max w uR uG}`, so
coefficients and modules here live in the universe `max w uG`. That is, `R : Type (max w uG)`
and the sheaves take values in `ModuleCat.{max w uG} R`, where `G : Type uG`. Write
`K = discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT`.

- `isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X`: every level of `K` vanishes
  in degrees `q ≥ D + 2`. This is the hypothesis `hN` of Worker 61's constructions, with row
  bound `N = D + 2`.
- `discreteGodementTruncatedCompactHomologyNatIso n`: Harris's (2.3), naturally in `m`. It is
  the generic natural isomorphism above for `Φ = discreteCompactSections J R L E`.
- `discreteGodementTruncatedCompactRepHomologyIso m n`: the degree-`n` cohomology of level `m`
  of `K.toRepComplexes` (the complexes of underlying representations) is
  `SmoothRep.toRep.obj (H^n_c(T m))`. It composes `mapHomologicalComplexHomologyIso` for the
  exact functor `SmoothRep.toRep` with (2.3).
- `discreteGodementTruncatedCompactRepHomology_ρ_eq_id`: if a subgroup acts trivially on every
  `H^q_c(T m)`, it acts trivially on the cohomology of level `m` of `K.toRepComplexes`.

The remaining data are a preorder `ι` that is filtered, and an antitone family `H : ι → Subgroup G`
of normal subgroups of finite index, with `Fintype` and `DecidableEq` instances on the
quotients. They also include Worker 61's hypotheses `hK` and `hk`:

- `hK`: every projection of `K` stays an epimorphism on `H i`-invariants;
- `hk`: the orders of the kernels of the projections `G ⧸ H j ⟶ G ⧸ H i` are invertible in
  `R`.

- `discreteGodementQuotientInvariantsLimit`: Harris's `C^•_m`. It is Worker 61's
  `quotientInvariantsLimit` with `N = D + 2`: the direct limit over `ι` of the inflated
  total complexes of the standard resolutions of the `H i`-invariants of `K`. It is an
  `ℓ`-divisible system of `ℤ`-graded complexes of representations of `G`.
- `discreteGodementQuotientInvariantsLimitToRepExtend`: Harris's comparison (2.6)
  `C^•_m ⟶ Γ_c(G^•_m)`. It is `quotientInvariantsLimitToRepExtend`, with target `K` extended
  by zero to `ℤ`.
- `quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend hS hP hR m htriv`: (2.6) is a
  quasi-isomorphism at level `m`. The hypotheses are `hS`, that every `H i` is a normal
  pro-`p` subgroup (`IsProPSubgroup p (H i)`), that `p` is invertible in `R`, and that every
  `H i` acts trivially on every `H^q_c(T m)` (`htriv`). This is Worker 61's
  `quasiIso_quotientInvariantsLimitToRepExtend`. Its trivial-action hypothesis on the
  cohomology of `K` is obtained from `htriv` by the previous lemma.
- `discreteGodementQuotientInvariantsLimitHomologyIso hS hP hR m htriv n`: Harris's (2.7),
  `Hⁿ(C^•_m) ≅ SmoothRep.toRep.obj (H^n_c(T m))`. It composes the isomorphism induced on
  cohomology by the quasi-isomorphism (2.6), the identification of the cohomology of a complex
  extended by zero (`extendHomologyNatIso`), and `discreteGodementTruncatedCompactRepHomologyIso`.
- `discreteGodementQuotientInvariantsInverseLimit`: Harris's `lim_m C^•_m`. It is
  `quotientInvariantsInverseLimit` with `N = D + 2`.
- `discreteGodementQuotientInvariantsInverseLimitHomologyIso hS hS' hP hR htriv hfin n`:
  Harris's Lemma 2.8,
  `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ SmoothRep.toRep.obj (H^n_c(T m)))`, an isomorphism in
  `Rep R G`. The hypotheses are `hS`, `hS'`, pro-`p`-ness, invertibility of `p`, trivial
  action of every `H i` on every `H^q_c(T m)` (`htriv`), and finiteness of every
  `H^q_c(T m)` (`hfin`). It composes four isomorphisms:
  - Worker 61's comparison `quotientInvariantsInverseLimitComparison`. It is an isomorphism by
    `isIso_quotientInvariantsInverseLimitComparison`, whose hypotheses on the cohomology of `K`
    follow from `htriv` and `hfin` through `discreteGodementTruncatedCompactRepHomologyIso`.
  - `extendLevelCohomologyLimitIso`.
  - The limit of `mapHomologicalComplexHomologyIso` for `SmoothRep.toRep`.
  - The limit of the natural isomorphism (2.3), whiskered by `SmoothRep.toRep`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ.
39 (1999), registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
§2, printed pp.305–306 = PDF pp.7–8. Worker 26 read the rendered pages.

- p.305: "For any integers `q ≥ 0` and `m > 0` it follows from Fact 1 bis and Lemma 2.2 that
  `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ)` is a finite smooth `S(ẽ)`-module. Thus there is an open normal
  pro-`p` subgroup `H ⊂ S(ẽ)` that acts trivially on `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ)` for all `q`
  and all `m`."
- p.306: "Taking the direct limit as `H` shrinks to the identity, we obtain an `ℓ`-divisible
  system of complexes `C^•_m` of projective `ℤ/ℓ^mℤ[S(e)]`-modules and a natural
  `S(ẽ)`-equivariant quasi-isomorphism (2.6) `C^•_m → G^•_m(U(e, N)_F̄)`. Now (2.3) and (2.6)
  imply that (2.7) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ H^q(C^•_m(U(ẽ)_F̄))`. [...] Lemma 2.8. For every
  `q`, there is a canonical isomorphism `H^q(lim_m C^•_m(U(ẽ)_F̄)) ⥲ lim_m
  H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ)`."

## Provenance and correspondence

This module specializes derived infrastructure. The correspondence with Harris is as
follows:

- `T` is an arbitrary `ℓ`-divisible system of discrete sheaves on a twisted site, and
  `H^n_c(T m)` is the published `discreteCompactDerived`. Harris's case is the constant system
  `ℤ/ℓ^mℤ` on `U(ẽ)` with the action of `S(ẽ)`. The constant system, `U(ẽ)`, `S(ẽ)` and the
  analytic site are not constructed here.
- Harris's subgroup `H` and its shrinking normal subgroups are an arbitrary filtered
  antitone family `H i` of normal subgroups of finite index. Harris derives the trivial
  action from Fact 1 bis and the finiteness of `H^q_c`. Here the trivial action (`htriv`) and
  the finiteness (`hfin`) are hypotheses on `H^q_c(T m)`. If one open normal pro-`p` subgroup
  acts trivially, so do its subgroups. Harris's specific family is not constructed.
- Harris states (2.7) as the composite of (2.3) and (2.6). Here (2.7) is the composite of the
  cohomology isomorphism of (2.6), the extension-by-zero identification and (2.3).
- Harris's Lemma 2.8 is "canonical" without a named map. Our map is Worker 61's comparison of
  Lemma 2.8 followed by the limit of the isomorphisms (2.3). The Mittag-Leffler argument is
  replaced, as in Worker 61's `InverseLimit`, by the hypothesis
  `FiniteCohomologyInverseLimitStatement`. The exactness of pro-`p` invariants on the
  relevant subcomplexes is the hypothesis `ProPInvariantSubcomplexStatement`.
- The naturality of (2.3) in `m` is ours. It is needed to form the limit over `m` of
  `H^n_c(T m)`.

## Not formalized here

Projectivity of the terms of `C^•_m`, the passage to `ℤ_ℓ`- or `ℚ_ℓ`-coefficients, the
statements `ProPInvariantSubcomplexStatement` and `FiniteCohomologyInverseLimitStatement`,
Fact 1 bis, and Harris's specific subgroups and spaces are not formalized here.
