# Harris's §2 constructions on the domains `U(f)` of Drinfeld's upper half space

Author: Worker 26. Builds on the following modules:

- `Langlands.Geometry.Analytic.DrinfeldFacetSpaces` (Worker 21). For a finite set `S` of
  vertices of the Bruhat–Tits building (`hS : S.Finite`), a real `ε` and a subgroup `H` of
  `GL_{d+1}(F)` contained in the stabilizer `facetStabilizer S` of `S`, it provides
  `facetAction K hS ε H hH`. This is Harris's open domain `U(f) = Res⁻¹(B(f, ε))` of
  Drinfeld's upper half space `Ω` over `K`, as an object of Worker 21's
  `LocalizedCategory.{u, u, u} (K := K)`, with the action of `H` restricted from the action
  `omegaAction` of `GL_{d+1}(F)` on `Ω`. Through it the module uses the open analytic
  domain `facetAnalyticDomain K hS ε` with carrier `facetDomain K S ε`, and the Hausdorff
  property of the space of `Ω`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRefinements` (Worker 26). It provides the
  three conditions (A) `HasFiniteCompactQuasiEtaleRefinements X`, (B)
  `HasCompactQuasiEtaleLifts ρ` and (C) `HasCompatibleCompactQuasiEtaleLifts ρ`, the
  derivation `hasCompactQuasiEtaleLifts_of_actionLiftStatement` of (B) from Worker 21's
  `QuasiEtaleActionLiftStatement`, and the reduction
  `hasFiniteEquivariantRefinements_compactLiftSystem` of the finite equivariant
  refinement condition to (A), (B) and (C).
- `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant` (Worker 26). It
  provides the constant `ℓ`-divisible system `quasiEtaleConstantSystem ρ R hℓ` of
  quasi-étale `G`-sheaves `R / ℓ ^ m R` on a `K`-analytic space with an action of `G`, and
  Harris's Lemma 2.2, Lemma 2.2 bis and (2.3) for it. Through it the module uses
  `AnalyticQuasiEtale` (Worker 26: Harris's (2.6), (2.7) and Lemma 2.8 for an arbitrary
  `ℓ`-divisible system of quasi-étale `G`-sheaves) and `AnalyticQuasiEtaleCompactCohomology`
  (Worker 26: Berkovich's `H^q_c(X{G}, -)`, `quasiEtaleGSheafCompactCohomology`).

The declarations about the space are in the namespace
`Langlands.Analytic.DrinfeldUpperHalfSpace`, the cohomological ones in
`Langlands.Cohomology.DivisibleSystem.Analytic`.

## Purpose

Harris carries out his §2 constructions on the domains `U(ẽ)` with the action of the
groups `S(ẽ)`. The published modules `AnalyticQuasiEtale` and
`AnalyticQuasiEtaleConstant` carry them out for an arbitrary `K`-analytic space `X` with an
action `ρ` of an arbitrary topological group `G`, assuming the finite equivariant
refinement condition. This module specializes them to an actual space of Harris's kind:
the open domain `U(f)` of Drinfeld's upper half space `Ω`, with the action of a subgroup
`H` of the stabilizer `S(f)` of `f` in `GL_{d+1}(F)`. It also reduces the refinement
condition on `U(f)` to the three conditions (A), (B), (C) of
`AnalyticQuasiEtaleRefinements` and continuity of the action. These inputs remain
hypotheses.

## Data and universes

- `F : Type u` is a nontrivially normed field with `[ProperSpace F]`, and `K : Type u` a
  complete ultrametric nontrivially normed field with `[NormedAlgebra F K]`. Harris works
  with `U(ẽ)_F̄`; here `K` is arbitrary.
- `d : ℕ` with `[NeZero d]` (so `d ≥ 1`); `Ω` is Drinfeld's upper half space of dimension
  `d` over `K`, with the action of `GL_{d+1}(F)`.
- `S : Set (NormClass F (Fin (d + 1) → F))` with `hS : S.Finite`, and `ε : ℝ`. The domain
  `U(f)` is defined for every such `S`; a facet is a special case.
- `H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)` with
  `hH : H ≤ facetStabilizer S`, where `facetStabilizer S` is the stabilizer of the set `S`
  in `GL_{d+1}(F)`. `H` carries the subspace topology of `GL_{d+1}(F)`. Since `F` and `H`
  live in the universe `u` of `K`, the inverse limit constructions of `AnalyticQuasiEtale`,
  which need `G : Type u`, apply to `H`.
- `R : Type (max u (u + 1) uL)` is a commutative ring. This is the coefficient universe
  `w = max u (v + 1) uL` of `AnalyticQuasiEtale` with `v = u`.

## The space and the refinement condition

- `facetSpace K hS ε H hH` (abbreviation): `(facetAction K hS ε H hH).V`, the space `U(f)`.
- `facetρ K hS ε H hH` (abbreviation): `(facetAction K hS ε H hH).ρAut`, the action of `H`
  on `U(f)` by automorphisms.
- `t2Space_facetSpace` (instance): the underlying space of `U(f)` is Hausdorff. It is the
  subspace `facetDomain K S ε` of the Hausdorff space of `Ω`.
- `hasFiniteEquivariantRefinements_facet K hS ε H hH hKL hc hA hC` (theorem): the finite
  equivariant refinement condition
  `(compactLiftSystem (facetρ K hS ε H hH)).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology (facetρ K hS ε H hH))`. Its hypotheses are:
  - `hKL : QuasiEtaleActionLiftStatement.{u, u, u} K`, Worker 21's published, unproved
    statement of Berkovich's lifts of actions to compact quasi-étale objects;
  - `hc : IsContinuousAction (facetρ K hS ε H hH)`, continuity of the action of `H` on
    `U(f)`;
  - `hA`: condition (A) for `U(f)`;
  - `hC`: condition (C) for the action of `H` on `U(f)`.

  Proof: condition (B) follows from `hKL`, the Hausdorff property `t2Space_facetSpace` and
  `hc` by `hasCompactQuasiEtaleLifts_of_actionLiftStatement`; then
  `hasFiniteEquivariantRefinements_compactLiftSystem` applies to (A), (B) and (C).

The cohomological declarations below take the refinement condition as an instance
argument. A user supplies it, for example, by
`haveI := hasFiniteEquivariantRefinements_facet K hS ε H hH hKL hc hA hC`.

## Constant coefficients on `U(f)`

The following take the field `L : Type uL` with `[NormedField L] [NormedAlgebra K L]`
and the point axioms `h : ∀ x, QuasiEtaleSite.PointAxioms L x` at the `L`-valued points of
`U(f)`, as in `AnalyticQuasiEtale`. Let `ℓ : ℕ` with `hℓ : IsSMulRegular R (ℓ : R)`.

- `FacetQuasiEtaleSheaf K hS ε H hH R` (abbreviation): quasi-étale `H`-sheaves of
  `R`-modules on `U(f)`, `QuasiEtaleGSheaf (facetρ K hS ε H hH) (ModuleCat R)`.
- `facetCompactCohomology K hS ε H hH R L h q` (abbreviation): Berkovich's
  `H^q_c(U(f){H}, -)`, the functor from these sheaves to smooth representations of `H`
  (`quasiEtaleGSheafCompactCohomology`).
- `facetConstantSystem K hS ε H hH R hℓ` (abbreviation): the constant `ℓ`-divisible system
  `{R / ℓ ^ m R}` of quasi-étale `H`-sheaves on `U(f)` (`quasiEtaleConstantSystem`).

The next declarations take the hypotheses of `AnalyticQuasiEtaleConstant`:

- exactness of the quasi-étale Godement functor of `U(f)` (instance arguments
  `PreservesFiniteLimits` and `PreservesFiniteColimits`, Harris's Fact 3);
- `hpoints`: the fibre functors at the `L`-valued points of `U(f)` are jointly faithful;
- a natural number `D`.

The declarations are:

- `facetConstantGodementResolutionSystem` (abbreviation): Harris's Lemma 2.2 on `U(f)`, the
  `ℓ`-divisible system of Godement resolutions of the constant sheaves `R / ℓ ^ m R`
  (`quasiEtaleConstantGodementResolutionSystem`).
- `facetConstantGodementTruncatedResolutionSystem D` (abbreviation): Harris's Lemma 2.2
  bis on `U(f)`, the truncations `G^•_m = τ_{≤ D+1}(F^•_m)`.
- `quasiIso_facetConstantGodementTruncatedAugmentation D m` (theorem): the augmentation from
  the constant sheaf `R / ℓ ^ m R` to `G^•_m` is a quasi-isomorphism
  (`quasiIso_quasiEtaleConstantGodementTruncatedAugmentation`).

With two further hypotheses:

- `hF`: Godement sheaves are acyclic for `Γ_{c,U(f){H}}`, that is,
  `H^{r+1}_c(U(f){H}, -)` vanishes on them;
- `hdim`: `H^n_c(U(f){H}, R / ℓ ^ m R) = 0` for all `m` and all `n > D`, for the constant
  quasi-étale `H`-sheaves of the modules `R ⧸ Ideal.span {ℓ ^ m}` (Harris's Fact 2 for
  constant coefficients; this is the hypothesis `hC` of `AnalyticQuasiEtaleConstant`);

the declarations are:

- `facetConstantCompactSectionsSystem` (abbreviation): Harris's `ℓ`-divisible system of
  finite-length complexes `Γ_{c,U(f){H}}(G^•_m)` of smooth representations of `H`
  (`quasiEtaleConstantCompactSectionsSystem`).
- `facetConstantCompactHomologyIso m n`: Harris's (2.3) on `U(f)`,
  `Hⁿ(Γ_{c,U(f){H}}(G^•_m)) ≅ H^n_c(U(f){H}, R / ℓ ^ m R)`, the published
  `quasiEtaleConstantCompactHomologyIso`.

## Lemma 2.8 on `U(f)`

The further data are those of the inverse limit part of `AnalyticQuasiEtale`, with
`G = H`: a filtered preorder `ι : Type u`, an antitone family `N : ι → Subgroup H`
(`hN : Antitone N`) of normal subgroups of finite index with `Fintype` and `DecidableEq`
instances on the quotients `H ⧸ N i`, and

- `hK`: every projection of `facetConstantCompactSectionsSystem` stays an epimorphism on
  `N i`-invariants;
- `hk`: the orders of the kernels of the projections `H ⧸ N j ⟶ H ⧸ N i` are invertible
  in `R`.

The declarations are:

- `facetConstantQuotientInvariantsInverseLimit` (abbreviation): Harris's `lim_m C^•_m` on
  `U(f)` for the constant system, a `ℤ`-graded complex in `Rep R H`
  (`quasiEtaleGodementQuotientInvariantsInverseLimit` applied to `facetConstantSystem`;
  its hypothesis `hT` is obtained from `hdim` by
  `isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj`).
- `facetConstantQuotientInvariantsInverseLimitHomologyIso hPro hLim hP hR htriv hfin n`:
  Harris's Lemma 2.8 on `U(f)` for the constant system,
  `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ SmoothRep.toRep.obj (H^n_c(U(f){H}, T m)))` in `Rep R H`,
  where `T m` is level `m` of `facetConstantSystem`. It is the published
  `quasiEtaleGodementQuotientInvariantsInverseLimitHomologyIso`. Its hypotheses are the
  published, unproved statements `hPro : ProPInvariantSubcomplexStatement` and
  `hLim : FiniteCohomologyInverseLimitStatement R` (the hypotheses `hS` and `hS'` of the
  general version), that every `N i` is a pro-`p` subgroup (`hP`), that `p` is invertible
  in `R` (`hR`), that every `N i` acts trivially on every `H^q_c(U(f){H}, T m)`
  (`htriv`), and that these modules are finite (`hfin`).

The definition of the last declaration is preceded by
`set_option synthInstance.maxHeartbeats 60000`: instance search for the existence of the
limit in `Rep R H` exceeds the default limit at this specialization. This changes only the
time limit for instance search.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed pp.303–306 =
PDF pp.5–8. Worker 26 checked the p.303 passages on a rendering of the page for this
module; the pp.304–306 passages are those checked for `AnalyticQuasiEtale` and
`AnalyticQuasiEtaleConstant`.

- p.303: "The group `GJ` is as in [H1] or the appendix of [H2]; it is a `p`-adic group of
  the form `∏_j 𝓑(F_j)^× × ℚ_p^×`, where `𝓑` is a division algebra over a number field
  `E`, `{F_j}` is the set of `p`-adic completions of `E`, `F = F_1`, and `𝓑(F)` is the
  matrix algebra. Recall that the Drinfel'd upper half space `Ω` attached to the group
  `GJ` admits an admissible covering by open subsets denoted `U(e)` in [H1, §2], where `e`
  runs through the set of facets in the Bruhat-Tits building `BT` attached to `GJ^ad`."
- p.303: "More generally, for every integer `N ≥ 1`, Drinfeld has constructed rigid
  analytic spaces `ℳ_N` admitting finite étale coverings `ℳ_N → ℳ_{N−1}`, with
  `ℳ_1 = Ω × Δ`, `Δ` the finitely generated free abelian group of algebraic characters of
  `GJ`. For each `δ ∈ Δ`, the inverse image of `U(e) × δ` in `ℳ_N` is denoted
  `U(e, N, δ)` [...] Henceforward, we write `ẽ` for the triple `(e, N, δ)`."
- p.303, Fact 2: "There is an integer `D > 0` such that `H^q_c(U, T) = 0` for all `q > D`
  and any étale morphism `U → U(ẽ)`."
- p.303: "Recall that the action of `GJ` on `Ω` lifts to an action on `ℳ_N`, and
  `U(ẽ)` is stabilized by a compact open subgroup `S(ẽ) ⊂ GJ`."
- p.304: "Lemma 2.2. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
  resolution `0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that, for each `q`, `{F_m^q}` is an
  `ℓ`-divisible system of `S(ẽ)`-modules over `U(ẽ)`."
- p.305: "We let `G_m^• = τ^{≤D+1}(F_m^•)`. [...] Lemma 2.2 bis. For each `m` the constant
  sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic resolution of finite length [...] Thus Lemma
  2.2 provides an isomorphism (2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q/B_m^q =
  H^q(G_m^•(U(ẽ)_F̄))`."
- p.306: "Lemma 2.8. For every `q`, there is a canonical isomorphism
  `H^q(lim_m C^•_m(U(ẽ)_F̄)) ⥲ lim_m H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ)`."

Harris's domains `U(e)` and the stabilizers `S(e)` are those of Harris 1997, §2, as cited
in `DrinfeldFacetSpaces`.

## Provenance and correspondence

- The space is `U(f) ⊆ Ω`, at the level of `Ω` itself. Harris's `U(ẽ) = U(e, N, δ)` lies
  in `ℳ_N`. For `N = 1` it is the inverse image of `U(e) × δ` in `ℳ_1 = Ω × Δ`, a copy of
  `U(e)`. The covering spaces `ℳ_N` for `N > 1` are not formalized.
- The group is a subgroup `H` of the stabilizer `S(f)` of `f` in `GL_{d+1}(F)`.
  `GL_{d+1}(F)` is the matrix factor `𝓑(F)^×` of Harris's group `GJ`, not `GJ` itself.
  Harris's `S(ẽ)` is a compact open subgroup of `GJ`. The stabilizer `S(f)` in
  `GL_{d+1}(F)` contains the centre, so it is not compact. No comparison of `H` with
  `S(ẽ)` is formalized, and compactness or openness of `H` is not assumed. The hypotheses
  on the subgroups `N i` (pro-`p`, finite index) are those of `AnalyticQuasiEtale`.
- `D` and `hdim` play the role of Harris's Fact 2 for the constant sheaves. Harris takes
  `D = 2 dim U(ẽ) = 2(n − 1)`; here `n = d + 1`, but `D` is arbitrary and `hdim` is a
  hypothesis.
- Harris's étale sheaves of `ℤ/ℓ^mℤ`-modules are replaced, as in `AnalyticQuasiEtale` and
  `AnalyticQuasiEtaleConstant`, by quasi-étale `H`-sheaves of `R`-modules with
  `R / ℓ ^ m R` in place of `ℤ/ℓ^mℤ`. The comparison with étale cohomology is not
  formalized.
- The reduction of the refinement condition to (A), (B), (C) is the published one of
  `AnalyticQuasiEtaleRefinements`. The only input specific to `U(f)` that this module
  proves is the Hausdorff property. Continuity of the action would follow from the
  published, unproved statements `OmegaActionContinuityStatement` (continuity on `Ω`) and
  `InvariantDomainContinuityStatement` (continuity on invariant domains), as explained in
  `DrinfeldFacetSpaces`; here it is the hypothesis `hc`.

## Not formalized here

The conditions (A) and (C) on `U(f)`, `QuasiEtaleActionLiftStatement`, continuity of the
action of `H` on `U(f)`, and all hypotheses inherited from `AnalyticQuasiEtale` and
`AnalyticQuasiEtaleConstant` (the point axioms, joint faithfulness of the points,
exactness and acyclicity of the Godement functor, Fact 2 for constant coefficients, the
subgroup family and its hypotheses, Worker 3's two statements, the trivial action and the
finiteness of `H^q_c`) remain hypotheses. The tower `ℳ_N`, the domains `U(e, N, δ)`,
Harris's group `GJ` and its subgroups `S(ẽ)`, and the comparison with étale cohomology are
not formalized here.
