# The action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` for quasi-étale `G`-sheaves

Author: Worker 26. This is the quasi-étale counterpart of `AnalyticEtaleRepCohomology` (this
candidate). Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedRepCohomology` (this candidate):
  `sheafGlobalRepDerived`, `sheafCompactRepDerived`, `restrictionGlobalCohomologyIso`,
  `restrictionCompactCohomologyIso`, and (via `TwistedLeftInduction`)
  `discrete_hasColimitsOfShape` and `discrete_hasExactColimitsOfShape`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology`: `quasiEtaleCohomology X R q`,
  the cohomology `H^q(X, F)` of module sheaves on the quasi-étale site of `X`.
- Through it, `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison`:
  `quasiEtaleGSheafRestriction ρ R` (Berkovich's `b^*`: inclusion of quasi-étale
  `G`-sheaves into sheaves on the twisted quasi-étale site, then restriction to the
  quasi-étale site of `X`), `quasiEtaleCompactCohomology L h R q` (`H^q_c(X, F)`, supports in
  the `L`-valued points) and `quasiEtale_enoughInjectives`. Also
  `AnalyticQuasiEtaleCompactCohomology` (`quasiEtale_hasSheafify`,
  `twistedQuasiEtale_hasSheafify`, `twistedQuasiEtale_enoughInjectives`,
  `quasiEtaleSite_locallySmall_points`), `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale`
  (`DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension`),
  `Langlands.Geometry.Analytic.OverSitePoints` (`QuasiEtaleSite.pointEquivariance L ρ h`),
  `AnalyticCompactSupport` (`pointTopology L X`, `continuousConstSMul_pointAction`),
  `EtaleGeometricPointEquivariance` (`EtaleSite.pointAction L ρ`) and `AnalyticGSheaves`
  (`QuasiEtaleGSheaf ρ A`, `compactLiftSystem ρ`).

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Setting

As in `AnalyticEtaleRepCohomology`: `K` a complete non-archimedean normed field,
`X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a group with a topology and
`[Small.{max u (v + 1) uL} G]`, `ρ : G →* Aut X`, `R : Type (max u (v + 1) uL)` a
commutative ring. No continuity of the group operations is assumed. A quasi-étale
`G`-sheaf `F` is an object of `QuasiEtaleGSheaf ρ (ModuleCat R)`, a sheaf on the twisted
quasi-étale site whose sections over compact objects are discrete for all lifts.

## Global sections

- `quasiEtaleRestrictionCohomologyRep ρ R q : QuasiEtaleGSheaf ρ (ModuleCat R) ⥤ Rep R G`:
  the inclusion `(compactLiftSystem ρ).discreteSheafInclusion` into sheaves on the twisted
  quasi-étale site, followed by `sheafGlobalRepDerived (quasiEtaleTopology X) R q`.
- `quasiEtaleRestrictionCohomologyForgetIso ρ R q`: an isomorphism
  `quasiEtaleRestrictionCohomologyRep ρ R q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCohomology X R q`. It is
  `restrictionGlobalCohomologyIso` whiskered by the inclusion of quasi-étale `G`-sheaves.
- `quasiEtaleRestrictionCohomologyAction ρ R q F : Representation R G` on
  `(quasiEtaleCohomology X R q).obj ((quasiEtaleGSheafRestriction ρ R).obj F)`, that is, on
  `H^q(X, b^*F)`: the representation `((quasiEtaleRestrictionCohomologyRep ρ R q).obj F).ρ`
  conjugated by the linear equivalence underlying the component of
  `quasiEtaleRestrictionCohomologyForgetIso` at `F` (`LinearEquiv.conjAlgEquiv`).
- `quasiEtaleRestrictionCohomologyAction_apply`: this component intertwines the two
  actions: `action g (e x) = e (ρ g x)`.

## Compactly supported sections

Let in addition `L : Type uL` be a normed field with `[NormedAlgebra K L]` and
`h : ∀ x, QuasiEtaleSite.PointAxioms L x` for all `L`-valued points `x` of `X`. Supports are
taken in the `L`-valued points, with the topology `pointTopology L X` and the action
`EtaleSite.pointAction L ρ`.

- `quasiEtaleRestrictionCompactCohomologyRep L ρ h R q`: the inclusion followed by
  `sheafCompactRepDerived (quasiEtaleTopology X) R (QuasiEtaleSite.pointEquivariance L ρ h) q`.
- `quasiEtaleRestrictionCompactCohomologyForgetIso L ρ h R q`: an isomorphism
  `quasiEtaleRestrictionCompactCohomologyRep L ρ h R q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCompactCohomology L h R q`.
- `quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F : Representation R G` on
  `H^q_c(X, b^*F)`, defined as in the global case.
- `quasiEtaleRestrictionCompactCohomologyAction_apply`: the intertwining property.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).

- Theorem 1.6.1(ii), printed p.13 = PDF p.13: "if `X` is compact, then for any quasi-étale
  (resp. étale) abelian sheaf `F` on `X(G)` one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in
  particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`."
- Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12, states the canonical action of `G`
  on `H^q_c(X, b^*F)` for étale abelian sheaves `F`: "In particular, the canonical action of
  `G` on the groups `H^q_c(X, b^*F)` is discrete [...]".

## Provenance and correspondence

`quasiEtaleRestrictionCohomologyAction` models the action of `G` on `H^q(X, b^*F)` used in
the quasi-étale case of Theorem 1.6.1(ii). Berkovich states Corollary 1.5.2 for étale
sheaves only; `quasiEtaleRestrictionCompactCohomologyAction` is the same construction for
quasi-étale `G`-sheaves (ours), parallel to the published quasi-étale compactly supported
cohomology `quasiEtaleGSheafCompactCohomology`. Berkovich does not define the action
explicitly. Here it comes from the right derived functors of the representation-valued
sections on the twisted quasi-étale site (`TwistedRepCohomology`). Berkovich's abelian
sheaves are replaced by sheaves of `R`-modules.

Not formalized here: that these actions are discrete (smooth), the isomorphisms with
`H^q(X{G}, F)` and `H^q_c(X{G}, F)` and their `G`-equivariance, and the spectral
sequences.
