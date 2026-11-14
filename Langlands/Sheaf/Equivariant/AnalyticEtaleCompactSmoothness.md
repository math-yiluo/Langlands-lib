# Smoothness of the action of `G` on `H^q_c(X, b^*F)`, granting Berkovich's comparison

Author: Worker 26. Builds on the following modules:

- `Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement` (Worker 16, accepted
  candidate `a205a1a2`): `AnalyticEtaleCompactComparisonStatement L X h G ρ R`, the statement
  without proof of the first assertion of Berkovich's Corollary 1.5.2(i) for étale sheaves. It
  says: if the underlying space of `X` is Hausdorff (`T2Space (localizedSpaceFunctor.obj X)`),
  every point of it underlies an `L`-valued point
  (`Function.Surjective (pointProjection L X)`), and the action is continuous
  (`IsContinuousAction ρ`), then `etaleCompactComparison L ρ h R q` is an isomorphism for
  every `q`.
- `Langlands.Sheaf.Equivariant.AnalyticRepSmoothness` (Worker 26, accepted candidate
  `3192666c`): `etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective`,
  `etaleRestrictionCompactCohomologySmoothRep` and `etaleCompactComparisonSmoothIso`. Through
  its imports: the comparison map `etaleCompactComparison L ρ h R q` from
  `H^q_c(X{G}, F)` (`etaleGSheafCompactCohomology L ρ h R q`, a smooth representation) to
  `H^q_c(X, b^*F)`, and the canonical action `etaleRestrictionCompactCohomologyAction L ρ h R q F`
  of `G` on `H^q_c(X, b^*F)`.
- `Langlands.Representation.Smooth.Transfer.PullbackProof`: `isSmooth_comp`, the restriction
  of a smooth representation along a continuous homomorphism is smooth.
- Mathlib: `ConcreteCategory.bijective_of_isIso`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Berkovich's Corollary 1.5.2(i) has two assertions: the comparison maps
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` are isomorphisms, and "in particular" the canonical action of
`G` on `H^q_c(X, b^*F)` is discrete, that is, smooth. Worker 16 states the first assertion
for étale sheaves as `AnalyticEtaleCompactComparisonStatement`. This module derives the second
assertion from it, so that the smoothness used in Harris 1997 Lemma 6(i) depends only on
that statement. The statement itself is not proved here.

## Setting

As in `AnalyticRepSmoothness`: `K : Type u` is a complete ultrametric normed field,
`X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a topological group with
`[Small.{max u (v + 1) uL} G]`, `ρ : G →* Aut X`, and the instance
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`. `L : Type uL`
is a normed field with `[NormedAlgebra K L]`, `h : ∀ x, EtaleSite.PointAxioms L x` for the
`L`-valued points `x` of `X`, and `R : Type (max u (v + 1) uL)` a commutative ring. Supports are
taken in the `L`-valued points. These are the binders of `AnalyticEtaleCompactComparisonStatement`.

Each declaration takes `hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R`,
`hT : T2Space (localizedSpaceFunctor.obj X)`, `hS : Function.Surjective (pointProjection L X)`,
`hρ : IsContinuousAction ρ`, a degree `q : ℕ` and an étale `G`-sheaf of modules `F`.

## Declarations

- `etaleCompactComparison_app_bijective_of_statement L ρ h R hB hT hS hρ q F` (theorem): the
  linear map underlying `(etaleCompactComparison L ρ h R q).app F` is bijective. Proof: `hB`
  applied to `hT`, `hS`, `hρ` and `q` gives `IsIso (etaleCompactComparison L ρ h R q)`, hence
  `IsIso` of its component at `F`, and `ConcreteCategory.bijective_of_isIso` gives
  bijectivity.
- `etaleRestrictionCompactCohomologyAction_isSmooth_of_statement L ρ h R hB hT hS hρ q F`
  (theorem): the canonical action of `G` on `H^q_c(X, b^*F)` is smooth
  (`Langlands.IsSmooth`). This is `etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective`
  applied to the surjectivity part of the previous theorem.
- `etaleCompactComparisonSmoothIsoOfStatement L ρ h R hB hT hS hρ q F` (definition): the
  isomorphism of smooth representations from `(etaleGSheafCompactCohomology L ρ h R q).obj F`
  to `etaleRestrictionCompactCohomologySmoothRep L ρ h R q F _`, which is
  `etaleCompactComparisonSmoothIso` for the bijectivity of the first theorem.
- `etaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement L ρ h R hB hT hS hρ q F H`
  (theorem): for any subgroup `H` of `G`, with the subspace topology, the restriction
  `(etaleRestrictionCompactCohomologyAction L ρ h R q F).comp H.subtype` of the canonical
  action to `H` is smooth. Proof: `isSmooth_comp` along the continuous inclusion `H → G`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`), Corollary
1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any étale abelian sheaf `F` on `X(G)` there are
canonical isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0` [sic, for `q ≥ 0`]. In
particular, the canonical action of `G` on the groups `H^q_c(X, b^*F)` is discrete and there is
a spectral sequence `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)`."

## Provenance and correspondence

Derived. Berkovich's "discrete" action is a smooth action in the sense of `Langlands.IsSmooth`:
every vector is fixed by an open subgroup. Berkovich obtains the discreteness from the
comparison isomorphism ("In particular"); this module formalizes that step, with the
comparison isomorphism taken from Worker 16's statement as a hypothesis. The hypotheses
`hT`, `hS` and `hρ` are those of the statement. As explained in the statement's Markdown,
`hS` is not in Berkovich: it makes the supports in `L`-valued points agree with Berkovich's
supports in all points. The restriction to a subgroup `H` is our addition, for subgroups such
as Harris's `GJ^0 ⊂ GJ` (Harris 1997 (A.8), recorded in the Library's coverage note
`notes/henniart/harris-cohomology-coverage.md`).

Not formalized here: a proof of `AnalyticEtaleCompactComparisonStatement`, the spectral
sequence of Corollary 1.5.2(i), and the quasi-étale analogue of these consequences for
`H^q_c`. The quasi-étale compact comparison is not stated in the Library: the coverage note
explains that on the current quasi-étale model it fails already in degree 0. The quasi-étale
consequences for `H^q` with compact `X` are in `AnalyticRepSmoothness`. No unconditional
smoothness of the action on `H^q_c(X, b^*F)` is proved.
