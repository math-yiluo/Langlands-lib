# Smoothness of the action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)`

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.AnalyticRepComparison` (accepted candidate `a8d99f4f`):
  the equivariance theorems `etaleComparison_representation`,
  `etaleCompactComparison_representation`, `quasiEtaleComparison_representation` and
  `quasiEtaleCompactComparison_representation`. Each says that the comparison map
  `H^q(X{G}, F) → H^q(X, b^*F)` (resp. `H^q_c(X{G}, F) → H^q_c(X, b^*F)`) carries the action
  of `g ∈ G` on its source to the canonical action of `g` on its target. Through its imports:
  the comparison maps `etaleComparison`, `etaleCompactComparison`, `quasiEtaleComparison` and
  `quasiEtaleCompactComparison`, the smooth representations `etaleGSheafCohomology`,
  `etaleGSheafCompactCohomology`, `quasiEtaleGSheafCohomology` and
  `quasiEtaleGSheafCompactCohomology` (Berkovich's `H^q(X{G}, F)` and `H^q_c(X{G}, F)`), the
  canonical actions `etaleRestrictionCohomologyAction`,
  `etaleRestrictionCompactCohomologyAction`, `quasiEtaleRestrictionCohomologyAction` and
  `quasiEtaleRestrictionCompactCohomologyAction` (published candidate `9abc9653`), and
  `smoothForget R G`.
- `Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement` (Worker 16):
  `AnalyticQuasiEtaleGlobalComparisonStatement X G ρ R`, the statement without proof of the
  quasi-étale case of Berkovich's Theorem 1.6.1(ii). It says: if `IsCompactSpace X` and
  `IsContinuousAction ρ`, then `quasiEtaleComparison ρ R q` is an isomorphism for every `q`.
- `Langlands.Representation.Category.Basic`: `SmoothRep R G` (the full subcategory of `Rep R G`
  of smooth representations), `SmoothRep.of`, `SmoothRep.ofHom`, `SmoothRep.mkIso` and
  `SmoothRep.isSmooth`. Through it, `Langlands.Representation.Smooth.Definitions`:
  `fixedVectors`, `IsSmoothVector` and `IsSmooth`.
- Mathlib: `Representation.IntertwiningMap`, `LinearMap.intertwiningMap_of_isIntertwiningMap`,
  `Representation.IntertwiningMap.ofBijective` and `ConcreteCategory.bijective_of_isIso`.

## Generic lemmas (namespace `Langlands`)

Let `R` be a commutative ring, `G` a group with a topology, and `ρ`, `σ` representations of
`G` on `R`-modules `V` and `W`.

- `Langlands.isSmoothVector_map f hv`: for an intertwining map `f : ρ.IntertwiningMap σ`,
  if `v` is fixed by an open subgroup `U` (`IsSmoothVector ρ v`), then `f v` is fixed by `U`
  (`IsSmoothVector σ (f v)`).
- `Langlands.isSmooth_of_surjective f hf hρ`: if `f` is surjective and `ρ` is smooth,
  then `σ` is smooth.

The Library's `isSmoothVector_of_finiteIntertwining` (in
`Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothVectors`) proves the first lemma
for an unbundled linear intertwiner. That module imports `L^2` automorphic material, so the
lemma is restated here for Mathlib's bundled `IntertwiningMap`.

## Setting of the analytic statements (namespace `Langlands.Sheaf.Equivariant.Analytic`)

`K : Type u` is a complete non-archimedean normed field,
`X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a topological group that is
`Small.{max u (v + 1) uL}`, `ρ : G →* Aut X`, and `R : Type (max u (v + 1) uL)` a
commutative ring. For étale `G`-sheaves (`EtaleGSheaf ρ (ModuleCat R)`) the hypothesis
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]` is
assumed. For quasi-étale `G`-sheaves (`QuasiEtaleGSheaf ρ (ModuleCat R)`) the hypothesis
`[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]` is
assumed. These are the hypotheses of `AnalyticRepComparison`. For compact supports,
`L : Type uL` is a normed field with `[NormedAlgebra K L]`, and
`h : ∀ x, EtaleSite.PointAxioms L x` (resp. `QuasiEtaleSite.PointAxioms L x`) for all
`L`-valued points `x` of `X`. Supports are taken in the `L`-valued points.

## Declarations for each comparison map

The same seven declarations are given for each of the four comparison maps. Below, `c` stands
for the component at `F` of the comparison map, `c.hom` for its underlying linear map,
`A` for the smooth representation `H^q(X{G}, F)` (resp. `H^q_c(X{G}, F)`), and `σ` for the
canonical action of `G` on `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`).

| Étale, `H^q` | Étale, `H^q_c` | Quasi-étale, `H^q` | Quasi-étale, `H^q_c` |
| --- | --- | --- | --- |
| `etaleComparisonIntertwiningMap` | `etaleCompactComparisonIntertwiningMap` | `quasiEtaleComparisonIntertwiningMap` | `quasiEtaleCompactComparisonIntertwiningMap` |
| `etaleRestrictionCohomologyAction_isSmooth_of_surjective` | `etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective` | `quasiEtaleRestrictionCohomologyAction_isSmooth_of_surjective` | `quasiEtaleRestrictionCompactCohomologyAction_isSmooth_of_surjective` |
| `etaleRestrictionCohomologySmoothRep` | `etaleRestrictionCompactCohomologySmoothRep` | `quasiEtaleRestrictionCohomologySmoothRep` | `quasiEtaleRestrictionCompactCohomologySmoothRep` |
| `etaleComparisonSmoothHom` | `etaleCompactComparisonSmoothHom` | `quasiEtaleComparisonSmoothHom` | `quasiEtaleCompactComparisonSmoothHom` |
| `etaleComparisonSmoothIso` | `etaleCompactComparisonSmoothIso` | `quasiEtaleComparisonSmoothIso` | `quasiEtaleCompactComparisonSmoothIso` |

For each column, with `q : ℕ` and `F` a `G`-sheaf:

- `*IntertwiningMap q F : A.representation.IntertwiningMap σ`, a definition: `c.hom`, made into
  an intertwining map by the equivariance theorem `*_representation` of
  `AnalyticRepComparison`. The theorem `*IntertwiningMap_apply` says that its value at `x`
  is `c.hom x` (by `rfl`).
- `*_isSmooth_of_surjective q F hs`, a theorem: if `hs : Function.Surjective c.hom`, then
  `IsSmooth σ`. This is `Langlands.isSmooth_of_surjective` applied to the intertwining
  map and the smoothness of `A`.
- `*SmoothRep q F hs : SmoothRep R G`, a definition: `SmoothRep.of σ` with the smoothness of
  the previous theorem. Its underlying module is `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`) and its
  action is `σ`.
- `*SmoothHom q F hs : A ⟶ *SmoothRep q F hs`, a definition: `SmoothRep.ofHom` of the
  intertwining map.
- `*SmoothIso q F hb : A ≅ *SmoothRep q F hb.2` for `hb : Function.Bijective c.hom`, a
  definition: `SmoothRep.mkIso` of `IntertwiningMap.ofBijective`. The theorem
  `*SmoothIso_hom` says that its forward morphism is `*SmoothHom q F hb.2` (by `rfl`).

The surjectivity and bijectivity of `c.hom` are hypotheses. They are not proved here.

## Consequences of Worker 16's statement (quasi-étale, `H^q`)

Assume `hB : AnalyticQuasiEtaleGlobalComparisonStatement X G ρ R`, `hX : IsCompactSpace X`
and `hρ : IsContinuousAction ρ`.

- `quasiEtaleComparison_app_bijective_of_statement ρ R hB hX hρ q F`, a theorem: the linear
  map underlying `(quasiEtaleComparison ρ R q).app F` is bijective. The proof applies `hB` to
  get `IsIso (quasiEtaleComparison ρ R q)`, hence `IsIso` of its component at `F`, and then
  `ConcreteCategory.bijective_of_isIso`.
- `quasiEtaleRestrictionCohomologyAction_isSmooth_of_statement ρ R hB hX hρ q F`, a theorem:
  the canonical action of `G` on `H^q(X, b^*F)` is smooth.
- `quasiEtaleComparisonSmoothIsoOfStatement ρ R hB hX hρ q F`, a definition: the isomorphism
  of smooth representations `quasiEtaleComparisonSmoothIso` for this bijectivity.

These results are conditional on `hB`, which is a hypothesis; it has not been proved.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).

- Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any étale abelian sheaf `F` on
  `X(G)` there are canonical isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0`
  [sic, for `q ≥ 0`]. In particular, the canonical action of `G` on the groups
  `H^q_c(X, b^*F)` is discrete and there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)`."
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: "if `X` is compact, then for any quasi-étale
  (resp. étale) abelian sheaf `F` on `X(G)` one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in
  particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`."

## Provenance and correspondence

Berkovich's "discrete" action is a smooth action in the sense of `Langlands.IsSmooth`: every
vector is fixed by an open subgroup. Berkovich derives the discreteness of the action on
`H^q_c(X, b^*F)` from the comparison isomorphism ("In particular"). This module formalizes
that step for the comparison maps and actions defined in this library: smoothness follows
from surjectivity of the comparison map, which is equivariant by `AnalyticRepComparison`.
This formulation is our own. Corollary 1.5.2(i) is stated for étale sheaves; the
quasi-étale `H^q_c` column applies the same step to the quasi-étale comparison map of
`AnalyticQuasiEtaleComparison`. Berkovich's abelian sheaves are replaced by sheaves of
`R`-modules. `H^q_c` uses supports in the `L`-valued points satisfying the point axioms, as
in `AnalyticEtaleComparison` and `AnalyticQuasiEtaleComparison`.

Not formalized here: the comparison isomorphisms themselves (Corollary 1.5.2(i), and
Theorem 1.6.1(ii) beyond the conditional consequences of Worker 16's statement), and the
spectral sequences. In particular, no unconditional smoothness of the action on
`H^q(X, b^*F)` or `H^q_c(X, b^*F)` is proved.

The generic smoothness-transfer lemmas are reused from
[Smooth/Transfer/SubquotientProof](../../Representation/Smooth/Transfer/SubquotientProof.md).
