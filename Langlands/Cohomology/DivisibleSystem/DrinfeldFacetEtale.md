# Harris's §2 constructions for étale sheaves on the domains `U(f)`

Author: Worker 26. Builds on the following modules:

- `Langlands.Cohomology.DivisibleSystem.DrinfeldFacet` (Worker 26, published): Harris's
  domain `U(f)` as the analytic space `facetSpace K hS ε H hH`, with the action
  `facetρ K hS ε H hH` of a subgroup `H` of the stabilizer `S(f)` in `GL_{d+1}(F)`, built
  from Worker 21's `facetAction` (`DrinfeldFacetSpaces`). It is the quasi-étale version of
  this module.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements` (Worker 26, published): the
  conditions `HasDistinguishedEtaleNeighbourhoods`, `HasDistinguishedEtaleLifts` and
  `HasCompatibleDistinguishedEtaleLifts`, and
  `hasAdmissibleRefinements_distinguishedLiftSystem`.
- `Langlands.Cohomology.DivisibleSystem.AnalyticEtaleConstant` (Worker 26, accepted or
  submitted before this module): the constant étale `G`-sheaves `etaleConstantSheaf`, the
  constant system `etaleConstantSystem`, Harris's Lemma 2.2, Lemma 2.2 bis, (2.3) and
  Lemma 2.8 for it with a family of points (`etaleConstantFamily*`), and
  `etaleConstantCompactHomologyToPlain`. Through it, `DivisibleSystem.AnalyticEtale`
  (`EtaleDivisibleSystem`, `etaleFamilyGodementFunctor`), `AnalyticEtaleComparison`
  (`etaleCompactCohomology`) and `AnalyticEtaleCompactCohomology`
  (`etaleGSheafCompactCohomology`, `twistedEtale_hasSheafify`, `etale_hasSheafify`).
- Worker 3's statements `ProPInvariantSubcomplexStatement` and
  `FiniteCohomologyInverseLimitStatement`, which appear only as hypotheses and are not
  proved in the Library.

`hasAdmissibleRefinements_facet` is in `Langlands.Analytic.DrinfeldUpperHalfSpace`; all other
declarations are in `Langlands.Cohomology.DivisibleSystem.Analytic`.

## Purpose

The published `DrinfeldFacet` specializes Harris's §2 constructions to `U(f)` on the
quasi-étale model, where the joint faithfulness of the `L`-valued points fails. Harris's
sheaves are étale. This module specializes the étale constructions instead: Berkovich's
étale `H`-sheaves on `U(f)`, the constant system `{R / ℓ ^ m R}`, Harris's Lemma 2.2,
Lemma 2.2 bis, (2.3) and Lemma 2.8, and the map from the cohomology of Harris's complexes to
the plain compactly supported étale cohomology of `U(f)`. As in
`DivisibleSystem.AnalyticEtale`, the Godement resolutions use an arbitrary family of points
of the étale site of `U(f)`.

## Data and universes

As in `DrinfeldFacet`:

- `F : Type u` is a nontrivially normed field with `[ProperSpace F]` (Harris's `F`), and
  `K : Type u` a complete ultrametric normed field with `[NormedAlgebra F K]`.
- `d ≥ 1` (`[NeZero d]`), a finite set `S` of norm classes on `F^{d+1}` (`hS : S.Finite`),
  the vertices of the facet `f`, and a real number `ε`.
- `H` is a subgroup of `GL_{d+1}(F)` with `hH : H ≤ facetStabilizer S`.
- Write `w = max u (u + 1) uL`. The ring `R : Type w` is commutative and
  `hℓ : IsSMulRegular R (ℓ : R)`.
- From the declarations after `FacetEtaleSheaf` on,
  `[(distinguishedLiftSystem (facetρ K hS ε H hH)).HasAdmissibleRefinements
  (twistedEtaleTopology (facetρ K hS ε H hH))]` is assumed.
- `L : Type uL` with `[NormedAlgebra K L]` and the point axioms
  `h : ∀ x, EtaleSite.PointAxioms L x` on `U(f)`, for compact supports.
- An index type `I : Type w` and a family
  `points : I → (etaleTopology (facetSpace K hS ε H hH)).Point.{w}`, with the exactness of
  the Godement functor of the family and `hpoints`.

## Declarations

- `hasAdmissibleRefinements_facet K hS ε H hH hA hB hC`: the admissible refinement
  condition for the étale `H`-sheaves on `U(f)` follows from the three conditions of
  `AnalyticEtaleRefinements` on `U(f)`. It is `hasAdmissibleRefinements_distinguishedLiftSystem`
  for `facetρ`. The topological group structure on `H` is the instance used by
  `DrinfeldFacet` and `facetAction`; no further hypothesis on `H` is added.
- `FacetEtaleSheaf K hS ε H hH R`: `EtaleGSheaf (facetρ K hS ε H hH) (ModuleCat R)`, the
  étale `H`-sheaves of `R`-modules on `U(f)`.
- `facetEtaleCompactCohomology ... q`: `H^q_c(U(f){H}, -)`, the published
  `etaleGSheafCompactCohomology` for `facetρ`.
- `facetEtaleConstantSystem ... hℓ`: the constant system `{R / ℓ ^ m R}` of étale
  `H`-sheaves (`etaleConstantSystem`).
- `facetEtaleConstantGodementResolutionSystem` and
  `facetEtaleConstantGodementTruncatedResolutionSystem ... D`: Harris's Lemma 2.2 and
  Lemma 2.2 bis on `U(f)` for the family `points`.
  `quasiIso_facetEtaleConstantGodementTruncatedAugmentation m`: level `m` of the truncation
  resolves the constant étale `H`-sheaf `R / ℓ ^ m R`.
- With `hF` (Godement sheaves acyclic for `Γ_{c,U(f){H}}`) and `hdim` (Harris's Fact 2 for
  the constant sheaves: `H^n_c(U(f){H}, R / ℓ ^ m R) = 0` for `n > D`):
  `facetEtaleConstantCompactSectionsSystem`, the system of complexes
  `Γ_{c,U(f){H}}(G^•_m)`, and `facetEtaleConstantCompactHomologyIso m n`, Harris's (2.3),
  `Hⁿ(Γ_{c,U(f){H}}(G^•_m)) ≅ H^n_c(U(f){H}, R / ℓ ^ m R)`.
- `facetEtaleConstantCompactHomologyToPlain m n`: the map from
  `Hⁿ(Γ_{c,U(f){H}}(G^•_m))`, with the action forgotten, to
  `H^n_c(U(f), R / ℓ ^ m R)`, the plain compactly supported cohomology of the constant sheaf
  on the étale site of `U(f)`: (2.3) followed by the comparison
  `etaleConstantCompactComparison`. That it is an isomorphism is not proved.
- With a filtered preorder `ι : Type u`, an antitone family `N : ι → Subgroup H` of normal
  subgroups of finite index and Worker 61's hypotheses `hK`, `hk`:
  `facetEtaleConstantQuotientInvariantsInverseLimit`, Harris's `lim_m C^•_m`, and
  `facetEtaleConstantQuotientInvariantsInverseLimitHomologyIso`, Harris's Lemma 2.8,
  `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ H^n_c(U(f){H}, R / ℓ ^ m R))` in `Rep R H`, under the
  pro-`p`, trivial-action and finiteness hypotheses. Its elaboration needs
  `synthInstance.maxHeartbeats 60000`, as in `DrinfeldFacet`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` (file SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), §2, printed pp.303–306
= PDF pp.5–8. The passages on `U(ẽ)`, `S(ẽ)`, Fact 2, Lemma 2.2, Lemma 2.2 bis, (2.3) and
Lemma 2.8 are quoted in the published `DrinfeldFacet.md`. Harris works with étale sheaves
(p.304 = PDF p.6, checked on a rendering of the page): "By an `ℓ`-divisible system of
`S(ẽ)`-modules over `U(ẽ)` we mean a collection `{T_m}` of étale sheaves in smooth
`ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`, `m ≥ 1`, [...]", and "Here `T` is an "étale sheaf in
smooth `ℤ/ℓ^mℤ[S(e)]`-modules" if, for any quasi-étale morphism `U → U(ẽ)` with `U` compact
the action of the stabilizer `S(ẽ)_U ⊂ S(ẽ)` on `T(U)` is smooth; in other words, `T` is
what Berkovich calls discrete." This is the condition of Berkovich's Definition 1.4.1 (see
`AnalyticEtaleComparison.md`).

## Provenance and correspondence

The correspondence is that of `DrinfeldFacet`, with Berkovich's étale `H`-sheaves in place of
the quasi-étale ones, which is closer to Harris. The same restrictions apply: the space is
`U(f) ⊆ Ω` (Harris's `U(ẽ)` for `N = 1`), the group is a subgroup `H` of the stabilizer of
`f` in `GL_{d+1}(F)` rather than Harris's compact open `S(ẽ) ⊂ GJ`, and `D` is arbitrary with
Fact 2 as the hypothesis `hdim`. Coefficients are `R / ℓ ^ m R`.

## Not formalized here

The three conditions of `AnalyticEtaleRefinements` on `U(f)`, the point axioms, a family of
points satisfying `hpoints`, exactness and acyclicity of the Godement functor, Fact 2 for
constant coefficients, the subgroup family and its hypotheses, Worker 3's two statements, the
trivial action and finiteness of `H^q_c`, that the comparison to plain cohomology is an
isomorphism, the tower `ℳ_N`, the domains `U(e, N, δ)`, Harris's group `GJ` and its
subgroups `S(ẽ)`.
