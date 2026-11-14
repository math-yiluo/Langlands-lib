# Equivariance of the comparison maps for étale and quasi-étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedRepComparison` (this candidate):
  `exactGlobalComparison_app_representation`, `exactGlobalComparison_app_apply` and their
  compactly supported analogues. For an exact functor `incl` into module sheaves on a twisted
  site, they factor the comparison maps through a morphism of representations.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology`: `etaleGSheafCohomology ρ R q`
  (Berkovich's `H^q(X{G}, F)` for étale `G`-sheaves, a smooth representation) and
  `etaleComparison ρ R q : H^q(X{G}, F) → H^q(X, b^*F)`, which is
  `exactGlobalComparison (etaleTopology X) R` for the inclusion
  `(distinguishedLiftSystem ρ).smoothSheafInclusion` of étale `G`-sheaves.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleComparison`: `etaleCompactComparison L ρ h R q :
  H^q_c(X{G}, F) → H^q_c(X, b^*F)`, which is `exactCompactComparison` for the same
  inclusion and `EtaleSite.pointEquivariance L ρ h`; `etale_enoughInjectives`,
  `etale_hasPointwiseRightKanExtension`. Through the imports,
  `AnalyticEtaleCompactCohomology` provides `etaleGSheafCompactCohomology L ρ h R q`,
  `etale_hasSheafify`, `twistedEtale_hasSheafify`, `twistedEtale_enoughInjectives` and
  `etaleGSheaf_enoughInjectives`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology` (through the imports) and
  `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison`: `quasiEtaleGSheafCohomology`,
  `quasiEtaleComparison ρ R q` (which is `globalComparison (quasiEtaleTopology X) R
  (compactLiftSystem ρ) q`), `quasiEtaleGSheafCompactCohomology` and
  `quasiEtaleCompactComparison L ρ h R q` (which is `compactComparison`), with the
  sheafification and injectivity facts for the quasi-étale sites.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleRepCohomology` and
  `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRepCohomology` (published candidate
  `9abc9653`): the canonical actions `etaleRestrictionCohomologyAction`,
  `etaleRestrictionCompactCohomologyAction`, `quasiEtaleRestrictionCohomologyAction` and
  `quasiEtaleRestrictionCompactCohomologyAction` of `G` on `H^q(X, b^*F)` and
  `H^q_c(X, b^*F)`, with the intertwining lemmas `*_apply` for their `ForgetIso`s.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Setting

`K : Type u` is a complete non-archimedean normed field,
`X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a topological group that is
`Small.{max u (v + 1) uL}`, `ρ : G →* Aut X`, and `R : Type (max u (v + 1) uL)` a
commutative ring. For étale `G`-sheaves (`EtaleGSheaf ρ (ModuleCat R)`) the hypothesis
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]` is
assumed. For quasi-étale `G`-sheaves (`QuasiEtaleGSheaf ρ (ModuleCat R)`) the hypothesis
`[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]` is
assumed. These are the hypotheses under which the comparison maps are defined. For
compact supports, `L : Type uL` is a normed field with `[NormedAlgebra K L]`, and
`h : ∀ x, EtaleSite.PointAxioms L x` (resp. `QuasiEtaleSite.PointAxioms L x`) for all
`L`-valued points `x` of `X`.

## Statements

For `F` a `G`-sheaf, `g : G` and `x ∈ H^q(X{G}, F)` (resp. `x ∈ H^q_c(X{G}, F)`):

- `etaleComparison_representation ρ R q F g x`:
  `etaleComparison (g · x) = etaleRestrictionCohomologyAction ρ R q F g (etaleComparison x)`,
  where `g · x` is `SmoothRep.representation` of `(etaleGSheafCohomology ρ R q).obj F`.
- `etaleCompactComparison_representation L ρ h R q F g x`: the same for
  `etaleCompactComparison` and `etaleRestrictionCompactCohomologyAction`.
- `quasiEtaleComparison_representation ρ R q F g x`: the same for `quasiEtaleComparison`
  and `quasiEtaleRestrictionCohomologyAction`.
- `quasiEtaleCompactComparison_representation L ρ h R q F g x`: the same for
  `quasiEtaleCompactComparison` and `quasiEtaleRestrictionCompactCohomologyAction`.

## Proofs

All four proofs follow the same pattern. The sheafification, enough-injectives and Kan
extension instances used in the definitions of the comparison map and of the action are
introduced locally. Then:

1. `exact*Comparison_app_representation` for `incl` the inclusion of `G`-sheaves gives
   `comparison (g · x) = c (g · y)`, where `y` is the image of `x` in the representation
   `etaleRestrictionCohomologyRep` (resp. its analogue) and `c` is
   `restrictionGlobalComparison` (resp. `restrictionCompactComparison`) at `incl F`.
   The inclusion is `(distinguishedLiftSystem ρ).smoothSheafInclusion` for étale sheaves and
   `(compactLiftSystem ρ).discreteSheafInclusion` for quasi-étale sheaves. The comparison
   maps of the analytic modules are definitionally the generic ones for these inclusions.
   For quasi-étale sheaves, `globalComparison` and `compactComparison` unfold to
   `exactGlobalComparison` and `exactCompactComparison`.
2. `exact*Comparison_app_apply` rewrites `comparison x` as `c y`.
3. The component of the `ForgetIso` of `AnalyticEtaleRepCohomology` (resp.
   `AnalyticQuasiEtaleRepCohomology`) at `F` is by definition `c`. So the intertwining lemma
   `*Action_apply` gives `c (g · y) = action g (c y)`.

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

Berkovich takes the action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` as canonical. He
deduces its discreteness from the isomorphisms with `H^q(X{G}, F)` and
`H^q_c(X{G}, F)`, which are smooth representations. This presupposes that those isomorphisms
are `G`-equivariant. The four theorems here prove this equivariance for the comparison maps
and the actions defined in this library. They are our own formulation. Berkovich's abelian
sheaves are replaced by sheaves of `R`-modules. `H^q_c` uses supports in the `L`-valued
points satisfying the point axioms, as in `AnalyticEtaleComparison` and
`AnalyticQuasiEtaleComparison`.

Not formalized here: that the comparison maps are isomorphisms (Corollary 1.5.2(i),
Theorem 1.6.1(ii)), and hence that the actions on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` are
smooth; the spectral sequences.
