# The constant `ℓ`-divisible system of étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.LocalActionSmoothConstant` (Worker 26, submitted with this
  module): the constant sheaf functor with values in locally discrete sheaves,
  `LocalActionSystem.smoothConstantSheaf L J R`, with its exactness and additivity.
- `Langlands.Cohomology.DivisibleSystem.ConstantCoefficients` (Worker 61): the
  `ℓ`-divisible system `scalarSystem R ℓ hℓ` of the modules `R / ℓ ^ m R`, for
  `hℓ : IsSMulRegular R (ℓ : R)`, the identification `scalarSystemObjIso hℓ m` of its level
  `m` with `R ⧸ Ideal.span {ℓ ^ m}`, and `DivisibleSystem.map` along exact additive functors.
- `Langlands.Cohomology.DivisibleSystem.AnalyticEtale` (Worker 26): `EtaleDivisibleSystem`,
  the Godement functor `etaleFamilyGodementFunctor` of a family of points of the étale site,
  and Harris's Lemma 2.2, Lemma 2.2 bis, (2.3) and Lemma 2.8 for étale `G`-sheaves.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleComparison` (Worker 26): Berkovich's `b^*`
  (`etaleGSheafRestriction`), the plain compactly supported cohomology
  `etaleCompactCohomology L h R q` on the étale site of `X`, the comparison
  `etaleCompactComparison L ρ h R q`, and `etale_hasPointwiseRightKanExtension`.
- `Langlands.Cohomology.DivisibleSystem.ConstantRestriction` (Worker 26):
  `constantSheafCompRestrictionIso`, the restriction of a constant sheaf on a twisted site.
- `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant` (Worker 26, through
  `ConstantRestriction`): `isSMulRegular_uLiftInt_natCast`.
- Through these modules: `AnalyticEtaleCompactCohomology` (sheafification on both sites,
  `etaleGSheafCompactCohomology`), Worker 21's étale site, points and point axioms, and
  Worker 3's statements `ProPInvariantSubcomplexStatement` and
  `FiniteCohomologyInverseLimitStatement`, which enter only as hypotheses `hS` and `hS'`
  and are not proved in the Library.

The generic declarations are in `Langlands.Cohomology.DivisibleSystem`. The étale `G`-sheaf
declarations up to Lemma 2.8 are in `Langlands.Cohomology.DivisibleSystem.Analytic`. The
restriction and comparison declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Harris states Lemma 2.2, Lemma 2.2 bis, (2.3) and Lemma 2.8 for the constant sheaves
`ℤ / ℓ ^ m ℤ`. `DivisibleSystem.AnalyticEtale` proves them for an arbitrary `ℓ`-divisible
system of étale `G`-sheaves. This module constructs the constant system of étale `G`-sheaves
and specializes those results to it. It mirrors the published quasi-étale modules
`AnalyticQuasiEtaleConstant`, the constant sections of `AnalyticQuasiEtalePoints`, and
`ConstantRestriction`. It also identifies `b^*` of a constant étale `G`-sheaf with the
constant sheaf on the étale site of `X`. Through this identification it maps the cohomology
of Harris's complexes to the plain compactly supported cohomology `H^n_c(X, R / ℓ ^ m R)`.

## The constant system of locally discrete sheaves

Let `L : LocalActionSystem T G` with a Grothendieck topology `J` on `T`,
`[HasSheafify J (ModuleCat.{w} R)]` and `[L.HasAdmissibleRefinements J]`, `R : Type w`
commutative and `hℓ : IsSMulRegular R (ℓ : R)`.

- `smoothConstantSystem L J R hℓ`: the `ℓ`-divisible system
  `(scalarSystem R ℓ hℓ).map (smoothConstantSheaf L J R)` of locally discrete sheaves.
  `DivisibleSystem.map` applies because the functor is additive and exact.
- `smoothConstantSystemObjIso L J R hℓ m`: level `m` is the constant sheaf of
  `R ⧸ Ideal.span {ℓ ^ m}`, the image of `scalarSystemObjIso hℓ m`.
- `smoothConstantSystem_projection`, `smoothConstantSystem_inclusion` (by `rfl`): the maps
  `j` and `i` of the system are the constant sheaf maps of those of `scalarSystem`.

## The constant system of étale `G`-sheaves

Data and universes are those of `DivisibleSystem.AnalyticEtale`: `K : Type u` a complete
ultrametric normed field, `X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` (in the
inverse-limit section `G : Type u`) with a topology and `ρ : G →* Aut X`,
`w = max u (v + 1) uL`, `R : Type w` commutative, `[Small.{w} G]`, and
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`. Uses carry
the explicit universes `.{u, v, uL}` where `uL` cannot be inferred.

- `etaleConstantSheaf ρ R`: the constant étale `G`-sheaf functor
  `ModuleCat R ⥤ EtaleGSheaf ρ (ModuleCat R)`, `smoothConstantSheaf` for the distinguished
  lift system on the twisted étale site. `etaleConstantSheaf_comp_inclusion` (by `rfl`):
  followed by the inclusion it is the constant sheaf functor of the twisted étale site.
- `etaleConstantSystem ρ R hℓ`: the constant system `{R / ℓ ^ m R}` of étale `G`-sheaves,
  and `etaleConstantSystemObjIso ρ R hℓ m` its levels.
  `etaleIntConstantSystem ρ hℓ`, for `ℓ ≠ 0`: the case `R = ULift ℤ`, Harris's
  `{ℤ / ℓ ^ m ℤ}`.
- `isZero_etaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC m n hn`: the bound
  `hC`, that `H^n_c(X{G}, R / ℓ ^ m R) = 0` for `n > D` (Harris's Fact 2 for the constant
  sheaves), transfers to the levels of the constant system. This gives the hypothesis `hT`
  of `AnalyticEtale` for the constant system.

## Lemma 2.2, Lemma 2.2 bis, (2.3) and Lemma 2.8 for the constant system

These take a family `points : I → (etaleTopology X).Point.{w}`, the exactness of
`etaleFamilyGodementFunctor ρ points R`, `hpoints`, and, from (2.3) on, `L`, `h`, `D`, `hF`
and `hC`, as in `AnalyticEtale`.

- `etaleConstantFamilyGodementResolutionSystem ρ points R hℓ hpoints`: Lemma 2.2 for the
  constant system.
- `etaleConstantFamilyGodementTruncatedResolutionSystem ρ points R hℓ hpoints D`: Lemma 2.2
  bis for it.
- `etaleConstantFamilyGodementTruncatedAugmentation m`: the augmentation
  `R / ℓ ^ m R ⟶ G^•_m` from the constant étale `G`-sheaf of `R ⧸ Ideal.span {ℓ ^ m}`: the
  augmentation of `AnalyticEtale` precomposed with `etaleConstantSystemObjIso`. By
  `quasiIso_etaleConstantFamilyGodementTruncatedAugmentation m` it is a quasi-isomorphism.
- `etaleConstantFamilyCompactSectionsSystem ρ points R hℓ L h hpoints D hF hC`: the system
  `Γ_{c,X{G}}(G^•_m)` for the constant system.
- `etaleConstantFamilyCompactHomologyIso m n`: Harris's (2.3),
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) ≅ H^n_c(X{G}, R / ℓ ^ m R)`.
- `etaleConstantFamilyQuotientInvariantsInverseLimit` and
  `etaleConstantFamilyQuotientInvariantsInverseLimitHomologyIso hS hS' hP hR htriv hfin n`:
  `lim_m C^•_m` and Harris's Lemma 2.8 for the constant system,
  `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ H^n_c(X{G}, R / ℓ ^ m R))` in `Rep R G`, where level `m` of
  the constant system stands for `R / ℓ ^ m R`. Its elaboration needs
  `synthInstance.maxHeartbeats 60000`, as in the quasi-étale version.

## Restriction of constant sheaves and the comparison with plain cohomology

- `etaleConstantSheafRestrictionIso ρ R`: Berkovich's `b^*` takes the constant étale
  `G`-sheaf `M` to the constant sheaf `M` on the étale site of `X`. Since
  `etaleConstantSheaf` followed by the inclusion is the constant sheaf of the twisted étale
  site, this is the published `constantSheafCompRestrictionIso` for the étale site.
- `etaleConstantCompactComparison L ρ h R q`: the comparison
  `H^q_c(X{G}, M) → H^q_c(X, M)`, natural in the module `M`: `etaleCompactComparison` at the
  constant étale `G`-sheaf `M`, followed by `H^q_c(X, -)` of the identification above.
  `etaleConstantCompactComparison_app` gives its components.
- `etaleConstantCompactHomologyToPlain m n`: the map
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) → H^n_c(X, R / ℓ ^ m R)`, with the action of `G` forgotten:
  Harris's (2.3) for the family `points`, followed by the constant comparison.

That these comparison maps are isomorphisms is not proved. With supports in the `L`-valued
points they are not isomorphisms in general; see "Supports in `L`-valued points" in
`AnalyticEtaleComparison.md`. That remark uses skyscraper sheaves, not constant ones;
whether the comparison for constant coefficients is an isomorphism has not been checked.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` (file SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), §2, printed pp.303–306
= PDF pp.5–8: Fact 2 (pp.303–304), Lemma 2.2 (p.304), Lemma 2.2 bis and (2.3) (p.305), and
Lemma 2.8 (p.306), stated for the constant sheaves `ℤ / ℓ ^ m ℤ`. The quotations are in the
Markdown of the published `AnalyticQuasiEtale`.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), Corollary 1.5.2(i),
printed pp.11–12, for the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)`; its quotation is in
`AnalyticEtaleComparison.md`.

## Provenance and correspondence

The correspondence with Harris and Berkovich is that of the published quasi-étale modules
`AnalyticQuasiEtaleConstant`, `AnalyticQuasiEtalePoints` and `ConstantRestriction`, with
Berkovich's étale `G`-sheaves in place of the quasi-étale ones. Harris's sheaves are étale,
so this is the closer model. Coefficients are `R / ℓ ^ m R` for a commutative ring `R` with
`ℓ` a non-zero-divisor; Harris's case is `R = ℤ` (`etaleIntConstantSystem`).

## Not formalized here

The hypotheses listed above (exactness of the Godement functor, a family of points
satisfying `hpoints`, `hF`, `hC`, the admissible refinements, the point axioms, Worker 3's
statements), that the comparison maps are isomorphisms, and Harris's spaces and groups.
