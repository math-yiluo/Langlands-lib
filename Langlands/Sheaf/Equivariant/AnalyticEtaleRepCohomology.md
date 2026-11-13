# The action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` for étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedRepCohomology` (this candidate): for a twisted site,
  `sheafGlobalRepDerived J R q` and `sheafCompactRepDerived J R E q` (right derived functors
  of the representation-valued global sections and compactly supported global sections),
  and the isomorphisms `restrictionGlobalCohomologyIso` and `restrictionCompactCohomologyIso`
  of their underlying modules with the cohomology of the restriction. It also provides, via
  `TwistedLeftInduction`, `discrete_hasColimitsOfShape` and
  `discrete_hasExactColimitsOfShape`.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology` (accepted candidate `a9296ab9`):
  `etaleCohomology X R q`, the cohomology `H^q(X, F)` of module sheaves on the étale site of
  `X`.
- Through it, `Langlands.Sheaf.Equivariant.AnalyticEtaleComparison`: `etaleGSheafRestriction ρ R`
  (Berkovich's `b^*`: inclusion of étale `G`-sheaves into sheaves on the twisted étale site,
  then restriction to the étale site of `X`), `etaleCompactCohomology L h R q`
  (`H^q_c(X, F)`, supports in the `L`-valued points), `etale_enoughInjectives` and
  `etale_hasPointwiseRightKanExtension`. Also `AnalyticEtaleCompactCohomology`
  (`etale_hasSheafify`, `twistedEtale_hasSheafify`, `twistedEtale_enoughInjectives`),
  `AnalyticCompactSupport` (`pointTopology L X`, `continuousConstSMul_pointAction`,
  `etaleSite_locallySmall_points`), `Langlands.Geometry.Analytic.EtaleGeometricPointEquivariance`
  (`EtaleSite.pointAction L ρ`, `EtaleSite.pointEquivariance L ρ h`) and
  `AnalyticGSheaves` (`EtaleGSheaf ρ A`, `distinguishedLiftSystem ρ`).

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Setting

`K : Type u` is a complete non-archimedean normed field,
`X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a group with a topology,
`ρ : G →* Aut X`, and `R : Type (max u (v + 1) uL)` a commutative ring. `G` is assumed
`Small.{max u (v + 1) uL}`; then coproducts of modules indexed by `G` exist and are exact,
and the étale and twisted étale sites have sheafification and enough injectives. No
continuity of the group operations is assumed. An étale `G`-sheaf `F` is an object of
`EtaleGSheaf ρ (ModuleCat R)`, a sheaf on the twisted étale site whose sections are locally
discrete for the lifts on distinguished étale objects.

## Global sections

- `etaleRestrictionCohomologyRep ρ R q : EtaleGSheaf ρ (ModuleCat R) ⥤ Rep R G`: the
  inclusion `(distinguishedLiftSystem ρ).smoothSheafInclusion` into sheaves on the twisted
  étale site, followed by `sheafGlobalRepDerived (etaleTopology X) R q`.
- `etaleRestrictionCohomologyForgetIso ρ R q`: an isomorphism
  `etaleRestrictionCohomologyRep ρ R q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  etaleGSheafRestriction ρ R ⋙ etaleCohomology X R q`. It is `restrictionGlobalCohomologyIso`
  whiskered by the inclusion of étale `G`-sheaves.
- `etaleRestrictionCohomologyAction ρ R q F : Representation R G` on
  `(etaleCohomology X R q).obj ((etaleGSheafRestriction ρ R).obj F)`, that is, on
  `H^q(X, b^*F)`: the representation `((etaleRestrictionCohomologyRep ρ R q).obj F).ρ`
  conjugated by the linear equivalence underlying the component of
  `etaleRestrictionCohomologyForgetIso` at `F` (`LinearEquiv.conjAlgEquiv`).
- `etaleRestrictionCohomologyAction_apply`: this component intertwines the two actions:
  `action g (e x) = e (ρ g x)`.

## Compactly supported sections

Let in addition `L : Type uL` be a normed field with `[NormedAlgebra K L]` and
`h : ∀ x, EtaleSite.PointAxioms L x` for all `L`-valued points `x` of `X`. Supports are taken
in the `L`-valued points, with the topology `pointTopology L X` and the action
`EtaleSite.pointAction L ρ`.

- `etaleRestrictionCompactCohomologyRep L ρ h R q : EtaleGSheaf ρ (ModuleCat R) ⥤ Rep R G`:
  the inclusion followed by
  `sheafCompactRepDerived (etaleTopology X) R (EtaleSite.pointEquivariance L ρ h) q`.
- `etaleRestrictionCompactCohomologyForgetIso L ρ h R q`: an isomorphism
  `etaleRestrictionCompactCohomologyRep L ρ h R q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q`.
- `etaleRestrictionCompactCohomologyAction L ρ h R q F : Representation R G` on
  `(etaleCompactCohomology L h R q).obj ((etaleGSheafRestriction ρ R).obj F)`, that is, on
  `H^q_c(X, b^*F)`, defined as in the global case.
- `etaleRestrictionCompactCohomologyAction_apply`: the intertwining property.

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

`etaleRestrictionCompactCohomologyAction` models the canonical action of `G` on
`H^q_c(X, b^*F)` in Corollary 1.5.2(i), and `etaleRestrictionCohomologyAction` the action
on `H^q(X, b^*F)` used in the spectral sequence of Theorem 1.6.1(ii). Berkovich does not
define the action explicitly. Here it comes from the right derived functors of the
representation-valued sections on the twisted étale site (`TwistedRepCohomology`).
Berkovich's abelian sheaves are replaced by sheaves of `R`-modules, and `H^q_c` uses
supports in the `L`-valued points satisfying the point axioms, as in
`AnalyticEtaleComparison`.

Not formalized here: that these actions are discrete (smooth), the isomorphisms
`H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)` and `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and their
`G`-equivariance, and the spectral sequences.
