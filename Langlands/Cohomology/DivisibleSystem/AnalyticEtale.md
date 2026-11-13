# Harris's divisible systems for étale `G`-sheaves on analytic spaces

Author: Worker 26. Builds on the following modules:

- `Langlands.Cohomology.DivisibleSystem.TwistedExact` and
  `Langlands.Sheaf.Equivariant.TwistedExactGodement` (Worker 26, submitted with this module):
  Harris's §2 constructions for a coreflective exact subcategory of sheaves on a twisted
  site.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleComparison` (Worker 26):
  `etale_hasPointwiseRightKanExtension`, the right Kan extensions from the étale site to the
  twisted étale site.
- Through it, `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology` (Worker 26):
  `twistedEtale_hasSheafify`, `etale_hasSheafify`, `etaleGSheaf_enoughInjectives`,
  `etaleGSheafCompactCohomology` (`H^q_c(X{G}, -)`), and the additivity of the inclusion of
  étale `G`-sheaves; `Langlands.Sheaf.Equivariant.AnalyticCompactSupport` (Worker 26):
  `pointTopology`, `continuousConstSMul_pointAction`, `etaleSite_locallySmall_points` and
  `etaleGSheafCompactSections`; `Langlands.Sheaf.Equivariant.AnalyticGSheaves` (Worker 26):
  `twistedEtaleTopology`, `distinguishedLiftSystem` and `EtaleGSheaf`; and
  `Langlands.Sheaf.Equivariant.LocalActionSmoothPart` (Worker 26): `smoothCoreflector`,
  `smoothAdjunction`, the abelian structure of locally discrete sheaves and the exactness,
  fullness and faithfulness of their inclusion.
- Worker 21's étale site `EtaleSite`, its topology `etaleTopology`, the point axioms
  `EtaleSite.PointAxioms`, the action `EtaleSite.pointAction` and
  `EtaleSite.pointEquivariance`; Worker 3's statements `ProPInvariantSubcomplexStatement`
  and `FiniteCohomologyInverseLimitStatement`, which appear only as hypotheses `hS` and
  `hS'` and are not proved in the Library.

## Purpose

The published modules `AnalyticQuasiEtale` and `AnalyticQuasiEtalePoints` specialize Harris's
§2 constructions to quasi-étale `G`-sheaves. As `AnalyticQuasiEtalePoints.md` explains, their
hypothesis `hpoints` fails on the quasi-étale site for the `L`-valued points, and for every
family of points that sees only points of Berkovich's space. This module specializes the
same constructions to Berkovich's étale `G`-sheaves `EtaleGSheaf`, through
`DivisibleSystem.TwistedExact`. The Godement resolutions use an arbitrary family of points
of the étale site of `X`, and the compactly supported cohomology is
`etaleGSheafCompactCohomology` of `AnalyticEtaleCompactCohomology`. On the étale site the
obstruction of `AnalyticQuasiEtalePoints.md` does not arise in the same way; see the remark
below.

It defines:

- in `Langlands.Sheaf.Equivariant.Analytic`, `etaleGSheafAdjunction ρ R`, the adjunction
  between the inclusion of étale `G`-sheaves of modules and the locally discrete part
  (`LocalActionSystem.smoothAdjunction` for `distinguishedLiftSystem ρ`);
- in `Langlands.Cohomology.DivisibleSystem.Analytic`, the types `EtaleDivisibleSystem ρ R ℓ`
  and `EtaleComplexDivisibleSystem ρ R ℓ` of `ℓ`-divisible systems of étale `G`-sheaves and
  of complexes of them, and Harris's Lemma 2.2, Lemma 2.2 bis, (2.3), (2.6), (2.7) and
  Lemma 2.8 for them.

Every declaration instantiates a declaration of `TwistedExact` or `TwistedExactGodement`.

## Data and universes

As in `AnalyticEtaleCompactCohomology`:

- `K : Type u` is a complete ultrametric normed field and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `G` is a group with `ρ : G →* Aut X` and `[TopologicalSpace G]`. It lies in `Type z`,
  except in the inverse-limit section, where `G : Type u`. The compact-section and
  inverse-limit sections also assume `[IsTopologicalGroup G]`.
- Write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative, sheaves take values in
  `ModuleCat.{w} R`, and `[Small.{w} G]`.
- `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]` is
  assumed throughout. It makes `EtaleGSheaf ρ (ModuleCat R)` abelian with an exact inclusion
  and a right adjoint.
- An index type `I : Type w` and a family `points : I → (etaleTopology X).Point.{w}` of
  points of the étale site.
- The compact-section and inverse-limit sections also take `L : Type uL`, a normed field with
  `[NormedAlgebra K L]`, and the point axioms `h : ∀ x, EtaleSite.PointAxioms L x`, because
  `H^q_c(X{G}, -)` takes supports in the `L`-valued points.

The universe `uL` occurs in many of these declarations only inside `w`, so uses name the
universes explicitly, as in `etaleFamilyGodementFunctor.{u, v, uL} ρ points R` and
`etaleGSheafAdjunction.{u, v, uL} ρ R`.

## Hypotheses of Harris's constructions

- `[PreservesFiniteLimits (etaleFamilyGodementFunctor ρ points R)]` and
  `[PreservesFiniteColimits ...]`: the Godement functor is exact (Harris's Fact 3).
- `hpoints : JointlyFaithful fun i => (points i).sheafFiber`: the fibre functors of the
  family are jointly faithful on sheaves of `R`-modules on the étale site.
- `hF`: every `H^{r+1}_c(X{G}, G⁰(M))` vanishes, where `G⁰` is the Godement functor of the
  family.
- `hT`: `H^n_c(X{G}, T m) = 0` for all `m` and `n > D` (Harris's Fact 2).

## Declarations

Godement functor:

- `etaleFamilyGodementFunctor ρ points R`: `exactZeroFunctor` for the inclusion of étale
  `G`-sheaves and `smoothCoreflector`, an endofunctor of `EtaleGSheaf ρ (ModuleCat R)`: the
  locally discrete part of the induction to the twisted site of the product of the
  skyscraper sheaves at the points of the family.
- `etaleFamilyGodementCoaugmentation ρ points R`: its coaugmentation (`exactCoaugmentation`);
  `mono_etaleFamilyGodementCoaugmentation ρ points R hpoints F`: it is a monomorphism.

Godement resolutions (Lemma 2.2 and Lemma 2.2 bis), for `T : EtaleDivisibleSystem ρ R ℓ`:

- `etaleFamilyGodementResolutionSystem ρ points R T hpoints`: Lemma 2.2;
  `etaleFamilyGodementResolutionSystemObjIso m` identifies level `m` with the Godement
  complex `exactComplexFunctor` of `T m`; `etaleFamilyGodementResolutionSystem_obj_exactAt`
  gives exactness in positive degrees.
- `etaleFamilyGodementTruncatedResolutionSystem ρ points R T hpoints D`: Lemma 2.2 bis,
  `G^•_m = τ_{≤ D+1}(F^•_m)`, with `etaleFamilyGodementTruncatedResolutionHom` (a
  quasi-isomorphism at every level, `quasiIso_etaleFamilyGodementTruncatedResolutionHom`),
  `isZero_etaleFamilyGodementTruncatedResolutionSystem_obj_X`,
  `etaleFamilyGodementTruncatedAugmentation m` and
  `quasiIso_etaleFamilyGodementTruncatedAugmentation m`.

Compact sections and (2.3):

- `isZero_etaleGSheafCompactCohomology_familyTruncatedResolutionSystem_obj_X m i r`:
  `H^{r+1}_c(X{G}, G^i_m) = 0`.
- `etaleFamilyGodementTruncatedCompactSectionsSystem ρ points R L h T hpoints D hF hT`: the
  `ℓ`-divisible system of complexes `Γ_{c,X{G}}(G^•_m)` of smooth representations; by
  `etaleFamilyGodementTruncatedCompactSectionsSystem_obj` (`rfl`), level `m` is
  `etaleGSheafCompactSections` applied termwise to `G^•_m`.
- `etaleFamilyGodementTruncatedCompactHomologyIso m n`: Harris's (2.3),
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) ≅ H^n_c(X{G}, T m)`.

Inverse limits, with `G : Type u`, a filtered preorder `ι : Type u`, an antitone family
`H : ι → Subgroup G` of normal subgroups of finite index and Worker 61's hypotheses `hK`
and `hk`:

- `etaleFamilyGodementQuotientInvariantsLimit`: Harris's `C^•_m`;
  `etaleFamilyGodementQuotientInvariantsLimitToRepExtend`: the comparison (2.6);
  `quasiIso_etaleFamilyGodementQuotientInvariantsLimitToRepExtend hS hP hR m htriv`: it is a
  quasi-isomorphism at level `m` if the `H i` are pro-`p`, `p` is invertible in `R`, and the
  `H i` act trivially on every `H^q_c(X{G}, T m)`.
- `etaleFamilyGodementQuotientInvariantsLimitHomologyIso`: (2.7),
  `Hⁿ(C^•_m) ≅ H^n_c(X{G}, T m)` in `Rep R G`.
- `etaleFamilyGodementQuotientInvariantsInverseLimit`: `lim_m C^•_m`;
  `etaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso hS hS' hP hR htriv hfin n`:
  Lemma 2.8, `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ H^n_c(X{G}, T m))` in `Rep R G`.

## Remark: points of the étale site

This remark is not formalized.

In Berkovich's étale topology a family `{f_i : U_i → U}` is a covering when
`U = ⋃ f_i(U_i)` (1993, §4.2, printed p.86). Berkovich defines the stalk `F_x` of an étale
sheaf at every point `x ∈ X`, as a discrete `G_{𝓗(x)}`-set, and proves (Corollary 4.2.3,
printed p.87) that a morphism of sheaves is a monomorphism, epimorphism or isomorphism if
and only if it is so on all stalks. The stalk functors are exact, so for abelian sheaves
this implies that they are jointly faithful. So the obstruction of
`AnalyticQuasiEtalePoints.md` does not apply: there, affinoid domains that are not
neighbourhoods give quasi-étale coverings that the `L`-valued points cannot detect.

It is not checked here that Worker 21's `etaleTopology` has these coverings, nor that a
family of points of the Library's étale site realizes Berkovich's stalks at all points of
`X`. For the `L`-valued points `EtaleSite.toPoint L x`, this would at least need every point
of `|X|` to be the image of an `L`-valued point. No family of points satisfying `hpoints` is
constructed, and the module does not claim that one exists. The compactly supported
cohomology takes supports in the `L`-valued points; for its relation to Berkovich's
supports see the remark "Supports in `L`-valued points" in `AnalyticEtaleComparison.md`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` (file SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), §2, printed pp.303–306
= PDF pp.5–8: Fact 2 and Fact 3 (pp.303–304), Lemma 2.2 (p.304), Lemma 2.2 bis and (2.3)
(p.305), (2.6), (2.7) and Lemma 2.8 (p.306). The quotations are in the Markdown of the
published `AnalyticQuasiEtale`. Harris works with étale sheaves on the analytic spaces
`U(ẽ)` and uses Berkovich's smooth `G`-equivariant Godement resolution (p.304).

Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78
(1993), registered as `berkovich-1993-etale-cohomology` (file SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`), cited in the remark:

- §4.2, printed p.86 = PDF p.83: the étale topology on a germ `(X, S)` is "generated by the
  pretopology for which the set of coverings of ((U, T) → (X, S)) ∈ Ét(X, S) is formed by
  the families {(U_i, T_i) → (U, T)}_{i∈I} such that T = ⋃_{i∈I} f_i(T_i)".
- §4.2, printed p.87 = PDF p.84: "The inverse image of a sheaf F with respect to i_x is
  denoted by F_x and is called the stalk of F at x." Corollary 4.2.3: "A morphism of sheaves
  F → G on (X, S) is a mono/epi/isomorphism if and only if for all x ∈ X the induced maps
  F_x → G_x possess the same properties."

## Provenance and correspondence

The correspondence with Harris is that of `AnalyticQuasiEtale` and
`AnalyticQuasiEtalePoints`, with Berkovich's étale `G`-sheaves in place of the quasi-étale
ones. Harris's statements concern étale sheaves, so this is the closer model; the
quasi-étale versions remain published. Taking an arbitrary family of points and the
coreflective generalization are ours (derived infrastructure).

## Not formalized here

A family of points of the étale site satisfying `hpoints`, the remark above, the other
hypotheses listed above, the constant system `R / ℓ ^ m R` of étale `G`-sheaves (Lemma
2.2 bis and (2.3) for it), Harris's spaces, groups and pro-`p` subgroups, and the comparison
with étale cohomology of schemes.
