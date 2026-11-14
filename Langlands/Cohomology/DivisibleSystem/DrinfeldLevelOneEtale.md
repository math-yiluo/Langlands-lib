# Étale `GL_{d+1}(F)`-sheaves and `H^q_c` on the level-one space `ℳ_1 = Ω × Δ`

Author: Worker 26. Builds on the following modules:

- `Langlands.Geometry.Analytic.DrinfeldLevelOneBase` (Worker 21, published):
  `levelOneBase K`, the level-one space `Ω × Δ` for the matrix factor `GL_{d+1}(F)` with its
  action, and `levelOneGSpace K hΩ hSI`, the same space as a `GL_{d+1}(F)`-space given
  continuity of the action on `Ω` (`hΩ`) and the published, unproved statement
  `SetInducedSpace.ContinuityStatement` (`hSI`). Through it, `omegaAction F K d`, the action
  on Drinfeld's upper half space `Ω`.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements` (Worker 26, published): the
  conditions `HasDistinguishedEtaleNeighbourhoods`, `HasDistinguishedEtaleLifts` and
  `HasCompatibleDistinguishedEtaleLifts`, and
  `hasAdmissibleRefinements_distinguishedLiftSystem`.
- `Langlands.Cohomology.DivisibleSystem.AnalyticEtaleConstant` (Worker 26, published): the
  constant étale `G`-sheaves `etaleConstantSheaf`, the constant system `etaleConstantSystem`,
  Harris's Lemma 2.2, Lemma 2.2 bis and (2.3) for it with a family of points
  (`etaleConstantFamily*`), and `etaleConstantCompactHomologyToPlain`. Through it,
  `DivisibleSystem.AnalyticEtale` (`EtaleDivisibleSystem`, `EtaleComplexDivisibleSystem`,
  `etaleFamilyGodementFunctor`), `AnalyticEtaleComparison` (`etaleCompactCohomology`) and
  `AnalyticEtaleCompactCohomology` (`EtaleGSheaf`, `etaleGSheafCompactCohomology`,
  `twistedEtale_hasSheafify`, `etale_hasSheafify`).
- `Langlands.Sheaf.Equivariant.AnalyticSubgroupRestriction` (Worker 26, published):
  `etaleGSheafSubgroupRestriction` and `etaleSubgroupRestrictionCompactCohomologyIso`.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactSmoothness` (Worker 26, published):
  `etaleCompactComparison_app_bijective_of_statement`,
  `etaleRestrictionCompactCohomologyAction_isSmooth_of_statement`,
  `etaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement` and
  `etaleCompactComparisonSmoothIsoOfStatement`. Through it, Worker 16's
  `AnalyticEtaleCompactComparisonStatement` (module
  `Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement`), which appears here only
  as a hypothesis and is not proved in the Library, and `AnalyticRepSmoothness`
  (`etaleRestrictionCompactCohomologySmoothRep`).

The first five declarations below (`levelOneSpace` to `isContinuousAction_levelOneρ`) are in
the namespace `Langlands.Analytic.DrinfeldUpperHalfSpace`, beside `levelOneBase`. All others
are in `Langlands.Cohomology.DivisibleSystem.Analytic`.

## Purpose

`DrinfeldLevelOneBase` constructs the space `Ω × Δ` with its action of `GL_{d+1}(F)`, but no
sheaves or cohomology on it. This module applies the published étale `G`-sheaf constructions
to that action: Berkovich's étale `GL_{d+1}(F)`-sheaves on `Ω × Δ`, their compactly supported
cohomology `H^q_c(ℳ_1{G}, -)` as smooth representations, the constant `ℓ`-divisible system
`{R / ℓ ^ m R}`, the analogues of Harris's Lemma 2.2, Lemma 2.2 bis and (2.3) for it, the map
to plain compactly supported cohomology, restriction to subgroups, and smoothness of the
canonical action of `GL_{d+1}(F)` on `H^q_c(ℳ_1, b^*F)` under Worker 16's comparison
statement. The only input specific to `Ω × Δ` that is used is that `levelOneGSpace` makes
the underlying space Hausdorff and the action continuous, given `hΩ` and `hSI`. Every
declaration is a specialization; no new construction is made.

## Data and universes

- `F : Type u` is a nontrivially normed field with `[ProperSpace F]` (Harris's `F`), and
  `K : Type u` a complete ultrametric nontrivially normed field with `[NormedAlgebra F K]`.
  `d ≥ 1` (`[NeZero d]`), as for `omegaAction`. `[IsUltrametricDist F]` is assumed only for
  `t2Space_levelOneSpace`, `isContinuousAction_levelOneρ` and the smoothness section, as
  for `levelOneGSpace`.
- The group is `GL_{d+1}(F) = Matrix.GeneralLinearGroup (Fin (d + 1)) F`, with Mathlib's
  topology on the units of the matrix ring.
- Write `w = max u (u + 1) uL`. The ring `R : Type w` is commutative and, where the constant
  system appears, `hℓ : IsSMulRegular R (ℓ : R)`.
- From `levelOneEtaleCompactCohomology` on (except in the restriction section),
  `[(distinguishedLiftSystem (levelOneρ F K d)).HasAdmissibleRefinements
  (twistedEtaleTopology (levelOneρ F K d))]` is assumed.
- `L : Type uL` with `[NormedAlgebra K L]` and the point axioms
  `h : ∀ x, EtaleSite.PointAxioms L x` on `Ω × Δ`, for supports in the `L`-valued points.
- For Lemma 2.2, Lemma 2.2 bis and (2.3): an index type `I : Type w` and a family
  `points : I → (etaleTopology (levelOneSpace F K d)).Point.{w}`, with exactness of its
  Godement functor (`PreservesFiniteLimits`, `PreservesFiniteColimits`) and `hpoints` (the
  stalk functors at `points` are jointly faithful). No such family is constructed and
  `hpoints` is not claimed for any family.

## Declarations

The space and its action:

- `levelOneSpace F K d`: the analytic space `(levelOneBase K).V`, Harris's `ℳ_1 = Ω × Δ`
  for the matrix factor.
- `levelOneρ F K d : GL_{d+1}(F) →* Aut (levelOneSpace F K d)`: the action
  `(levelOneBase K).ρAut`.
- `hasAdmissibleRefinements_levelOne F K d hA hB hC` (theorem): the admissible refinement
  condition of the étale `GL_{d+1}(F)`-sheaves on `Ω × Δ` follows from the three conditions of
  `AnalyticEtaleRefinements` on `Ω × Δ`. It is `hasAdmissibleRefinements_distinguishedLiftSystem`
  for `levelOneρ`. The three conditions remain hypotheses.
- `t2Space_levelOneSpace F K d hΩ hSI` and `isContinuousAction_levelOneρ F K d hΩ hSI`
  (theorems): given `hΩ` and `hSI`, the underlying space of `Ω × Δ` is Hausdorff and the
  action is continuous. They are the two components of `(levelOneGSpace K hΩ hSI).property`.

Sheaves, cohomology and the constant system:

- `LevelOneEtaleSheaf F K d R`: `EtaleGSheaf (levelOneρ F K d) (ModuleCat R)`, the étale
  `GL_{d+1}(F)`-sheaves of `R`-modules on `Ω × Δ`.
- `levelOneEtaleSubgroupRestriction F K d R H`: for any subgroup `H` of `GL_{d+1}(F)`, the
  restriction to étale `H`-sheaves for the action `(levelOneρ F K d).comp H.subtype`
  (`etaleGSheafSubgroupRestriction`).
- `levelOneEtaleCompactCohomology F K d R L h q`: Berkovich's `H^q_c(ℳ_1{G}, -)`,
  `G = GL_{d+1}(F)`, valued in smooth representations of `G`
  (`etaleGSheafCompactCohomology`).
- `levelOneEtaleConstantSystem F K d R hℓ`: the constant `ℓ`-divisible system
  `{R / ℓ ^ m R}` of étale `GL_{d+1}(F)`-sheaves (`etaleConstantSystem`).
- `levelOneEtaleConstantGodementResolutionSystem ... points hpoints` and
  `levelOneEtaleConstantGodementTruncatedResolutionSystem ... D`: the analogues of Harris's
  Lemma 2.2 and Lemma 2.2 bis on `Ω × Δ` for the family `points` (the Godement resolution
  system of the constant system, and its truncation `τ_{≤ D+1}`).
  `quasiIso_levelOneEtaleConstantGodementTruncatedAugmentation m` (theorem): level `m` of the
  truncation resolves the constant étale sheaf `R / ℓ ^ m R`.
- With `hF` (the Godement sheaves are acyclic for `Γ_{c,ℳ_1{G}}`: `H^{r+1}_c` of each
  vanishes) and `hdim` (`H^n_c(ℳ_1{G}, R / ℓ ^ m R) = 0` for `n > D`):
  `levelOneEtaleConstantCompactSectionsSystem`, the system of complexes
  `Γ_{c,ℳ_1{G}}(G^•_m)` of smooth representations of `G`, and
  `levelOneEtaleConstantCompactHomologyIso m n`, the analogue of Harris's (2.3),
  `Hⁿ(Γ_{c,ℳ_1{G}}(G^•_m)) ≅ H^n_c(ℳ_1{G}, R / ℓ ^ m R)`.
- `levelOneEtaleConstantCompactHomologyToPlain m n`: the map from
  `Hⁿ(Γ_{c,ℳ_1{G}}(G^•_m))`, with the action forgotten, to `H^n_c(ℳ_1, R / ℓ ^ m R)`, the
  plain compactly supported cohomology of the constant sheaf on the étale site of `Ω × Δ`
  (`etaleConstantCompactHomologyToPlain`). That it is an isomorphism is not proved.

Restriction to subgroups (no refinement instance needed):

- `levelOneEtaleSubgroupRestrictionCompactCohomologyIso F K d R L h H q`: for any subgroup
  `H` of `GL_{d+1}(F)`, the restriction to `H` of the representation of `GL_{d+1}(F)` on
  `H^q_c(ℳ_1, b^*F)` is the representation of `H` on `H^q_c(ℳ_1, b^*F|_H)`, naturally in the
  étale `GL_{d+1}(F)`-sheaf `F` (`etaleSubgroupRestrictionCompactCohomologyIso`). Examples of
  `H` are `detNormOne F d`, the stabilizer of every copy of `Ω` (`stabilizer_levelOneIndex`).

Smoothness, granting Worker 16's statement. Each declaration takes
`hB : AnalyticEtaleCompactComparisonStatement L (levelOneSpace F K d) h GL_{d+1}(F) (levelOneρ F K d) R`,
`hS : Function.Surjective (pointProjection L (levelOneSpace F K d))` (every point of `Ω × Δ`
underlies an `L`-valued point), `hΩ` and `hSI`, a degree `q` and an étale
`GL_{d+1}(F)`-sheaf `M`. Hausdorffness and continuity of the action, which the statement also
needs, come from `t2Space_levelOneSpace` and `isContinuousAction_levelOneρ`.

- `levelOneEtaleRestrictionCompactCohomologyAction_isSmooth_of_statement` (theorem): the
  canonical action of `GL_{d+1}(F)` on `H^q_c(ℳ_1, b^*M)` is smooth.
- `levelOneEtaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement`
  (theorem): its restriction to any subgroup `H` is smooth.
- `levelOneEtaleCompactComparison_app_bijective_of_statement` (theorem): the comparison map
  `H^q_c(ℳ_1{G}, M) → H^q_c(ℳ_1, b^*M)` is bijective.
- `levelOneEtaleCompactComparisonSmoothIsoOfStatement` (definition): the comparison as an
  isomorphism of smooth representations from `(levelOneEtaleCompactCohomology ... q).obj M`
  to `etaleRestrictionCompactCohomologySmoothRep ... q M _`.

Each proof is the corresponding published declaration applied to `levelOneρ`, with
`t2Space_levelOneSpace` and `isContinuousAction_levelOneρ` for the hypotheses `hT` and `hρ`.

## Original sources

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` (file SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), §2, printed p.303
(PDF p.5): "More generally, for every integer `N ≥ 1`, Drinfeld has constructed rigid
analytic spaces `ℳ_N` admitting finite étale coverings `ℳ_N → ℳ_{N−1}`, with
`ℳ_1 = Ω × Δ`, `Δ` the finitely generated free abelian group of algebraic characters of
`GJ`." and "Recall that the action of `GJ` on `Ω` lifts to an action on `ℳ_N` [...]". The
passages on Lemma 2.2 (p.304), Lemma 2.2 bis and (2.3) (p.305) are quoted in the published
`DrinfeldFacet.md` and `DrinfeldFacetEtale.md`; Harris's sheaves there are étale.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`, Corollary
1.5.2(i), printed pp.11–12: "For any étale abelian sheaf `F` on `X(G)` there are canonical
isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)` [...] In particular, the canonical action of
`G` on the groups `H^q_c(X, b^*F)` is discrete [...]" (quoted in full in
`AnalyticEtaleCompactSmoothness.md`). The restriction to subgroups follows Berkovich §1.4,
printed p.7, as explained in `AnalyticSubgroupRestriction.md`.

## Provenance and correspondence

Derived. Harris states Lemma 2.2, Lemma 2.2 bis and (2.3) for the domains `U(ẽ) ⊂ ℳ_N` with
the compact open stabilizers `S(ẽ)`; the published `DrinfeldFacetEtale` specializes them to
`U(f) ⊆ Ω`. This module applies the same general constructions (Berkovich's `X(G)` for any
`G`-space) to the whole level-one space `Ω × Δ` with the whole group `GL_{d+1}(F)`, on
which Harris's `GJ` acts through the lift of its action on `Ω` quoted above. The smoothness
results specialize those that `AnalyticEtaleCompactSmoothness` provides for Harris 1997
Lemma 6(i) (see the Library's coverage note `notes/henniart/harris-cohomology-coverage.md`)
to this space. The restrictions of `DrinfeldLevelOneBase` apply: the group is the matrix factor
`GL_{d+1}(F)` of Harris's `GJ`, not `GJ`; the index set is `GL_{d+1}(F) ⧸ detNormOne F d`.
Harris's `ℤ/ℓ^mℤ` is replaced by `R / ℓ ^ m R`, `D` is arbitrary with `hdim` in place of
Harris's Fact 2, and the Godement resolutions use an arbitrary family of points, as in
`DivisibleSystem.AnalyticEtale`. Harris's Lemma 2.8 is not specialized here.

## Not formalized here

The three conditions of `AnalyticEtaleRefinements` on `Ω × Δ`, the point axioms, `hS`, a
family of points satisfying `hpoints`, exactness and acyclicity of the Godement functor,
`hdim`, a proof of `AnalyticEtaleCompactComparisonStatement`, `hΩ` and `hSI` (published
statements that are still unproved), that the map to plain cohomology is an isomorphism, the
decomposition of `H^q_c(ℳ_1)` as an induced representation from the copies of `Ω`
(Harris 1997 (A.8) at level one), Harris's group `GJ`, the tower `ℳ_N` for `N ≥ 2` and its
domains `U(e, N, δ)`.
