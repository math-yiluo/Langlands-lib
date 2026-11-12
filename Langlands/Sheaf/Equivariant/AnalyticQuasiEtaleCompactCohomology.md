# Compactly supported cohomology of quasi-étale `G`-sheaves on analytic spaces

Author: Worker 26. Uses the published `Langlands.Sheaf.Equivariant.AnalyticCompactSupport`
(topology on `L`-valued points, Worker 26), `Langlands.Sheaf.Equivariant.AnalyticGSheaves`
(twisted quasi-étale site, lifts on compact objects, quasi-étale `G`-sheaves, Worker 26),
`Langlands.Sheaf.Equivariant.TwistedCompactSupport` (compactly supported sections and
their derived functors on discrete sheaves of a twisted site, Worker 26) and
`Langlands.Cohomology.DiscreteSheafDerivedComplex` (derived section complexes, Worker 26).
From Worker 21 it uses the quasi-étale site `QuasiEtaleSite` and the points of that
site given by `L`-valued points (`Langlands.Geometry.Analytic.OverSitePoints`:
`QuasiEtaleSite.PointAxioms`, `QuasiEtaleSite.toPoint`,
`QuasiEtaleSite.pointEquivariance`).

## Purpose

Let a group `G` act on a `K`-analytic space `X`. The module `AnalyticCompactSupport`
gives Berkovich's compactly supported sections `Γ_{c,X{G}}` on the twisted étale site.
It does not define their derived functors there, because the étale `G`-sheaves are
not known to form an abelian category with enough injectives. Berkovich's quasi-étale
`G`-sheaves `T_G(X_qét)`, modelled by `QuasiEtaleGSheaf`, are the discrete sheaves of
the local action system of lifts on compact quasi-étale objects. The published
`TwistedCompactSupport` takes derived functors on such categories of discrete sheaves.
This module specializes that construction to the quasi-étale site. It

- proves that the quasi-étale site and the twisted quasi-étale site are essentially
  small in the universe of the coefficients, and deduces that module sheaves on them
  have sheafification and that module sheaves on the twisted quasi-étale site have
  enough injectives;
- defines `Γ_c` and `Γ_{c,X{G}}` on the twisted quasi-étale site and on quasi-étale
  `G`-sheaves, with supports in the `L`-valued points;
- defines `H^q_c(X{G}, F)` for quasi-étale `G`-sheaves of modules and the complex
  `RΓ_c(X{G}, F)`.

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`. Both `QuasiEtaleSite X` and
  `TwistedOver quasiEtale ρ` have objects in `Type (max u (v + 1))`. Morphisms of
  `QuasiEtaleSite X` lie in `Type (max u (v + 1))`, and morphisms of the twisted site
  lie in `Type (max u (v + 1) z)`, because they also record a group element.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`. Write
  `P = localizedFieldPointFunctor L`.
- `G : Type z` is a group and `ρ : G →* Aut X`. The smooth parts and the cohomology
  use `[TopologicalSpace G] [IsTopologicalGroup G]`.
- Coefficients: `R : Type (max u (v + 1) uL)` is a commutative ring and sheaves take
  values in `ModuleCat.{max u (v + 1) uL} R`. This is the universe of Worker 21's
  points `QuasiEtaleSite.toPoint L x h`, which the published construction requires to
  be the universe of the modules. We write `w = max u (v + 1) uL`.
- `[Small.{w} G]` is assumed for the statements about the twisted site. It holds,
  for example, when `G` lies in a universe at most `w`.
- `h : ∀ x : P.obj X, QuasiEtaleSite.PointAxioms L x`: every `L`-valued point satisfies
  the point axioms of the quasi-étale site. This is a hypothesis. Worker 21's module
  proves no instance of it.

## Size, sheafification and injectives

These are theorems rather than instances. Their universe `uL` occurs only inside
`max u (v + 1) uL`, and Lean's instance search does not solve the resulting
universe constraints. The definitions below supply them locally with `haveI`.

- `quasiEtaleSite_locallySmall_points X` and `quasiEtaleSite_essentiallySmall_points X`:
  `QuasiEtaleSite X` is locally small and essentially small in universe `w`. Its
  objects and morphisms lie in `Type (max u (v + 1))`, so Mathlib's `small_lift`
  applies, and `essentiallySmall_of_small_of_locallySmall` concludes.
- `twistedQuasiEtale_locallySmall_points X ρ` (with `[Small.{w} G]`): the morphisms of
  the twisted quasi-étale site are small in `w`. A twisted morphism `U ⟶ V` is
  determined by its twist in `G` and its underlying arrow (`TwistedOver.Hom.ext`), so
  it injects into `G × (U.obj.left ⟶ V.obj.left)`.
- `twistedQuasiEtale_essentiallySmall_points X ρ`: the twisted quasi-étale site is
  essentially small in `w`.
- `quasiEtale_hasSheafify X R` and `twistedQuasiEtale_hasSheafify X ρ R`: module sheaves
  on both sites have sheafification. This is Mathlib's
  `hasSheafifyEssentiallySmallSite`, which sheafifies on a small model.
- `twistedQuasiEtale_enoughInjectives X ρ R`: `Sheaf (twistedQuasiEtaleTopology ρ)
  (ModuleCat R)` has enough injectives. Mathlib's
  `Sheaf.isGrothendieckAbelian_of_essentiallySmall` shows that it is a Grothendieck
  abelian category, and `IsGrothendieckAbelian.enoughInjectives` concludes. The limits
  over the comma categories `StructuredArrow Y (equivSmallModel _).inverse.op` that the
  first lemma needs exist because these categories are essentially small in `w`
  (Mathlib's `StructuredArrow.essentiallySmall` and
  `hasLimitsOfShape_of_essentiallySmall`).

Under the finite equivariant refinements of the next sections, the published
`discreteSheaf_enoughInjectives` then gives enough injectives for the quasi-étale
`G`-sheaves as well.

## Supports

- `quasiEtalePoints L h x` is Worker 21's point `QuasiEtaleSite.toPoint L x (h x)` of
  the quasi-étale topology, in universe `w`. Its fibre over a quasi-étale `U → X` is
  the set of `L`-valued points of `U` over `x`.
- `isCompactlySupported_quasiEtalePoints_iff L h s`: for a presheaf `F` of modules on
  `QuasiEtaleSite X`, an object `U` and `s ∈ F(U)`, the section `s` is compactly
  supported for the family `quasiEtalePoints L h` (with the topology `pointTopology L X`
  of `AnalyticCompactSupport`) exactly when the image of its support in `|X|` lies in a
  compact subset of `|X|` made of underlying points of `L`-valued points. This is
  `exists_isCompact_superset_iff` of `AnalyticCompactSupport`, as in the étale case.

## Compactly supported sections

In all the following, the topology `pointTopology L X`, Worker 21's action
`EtaleSite.pointAction L ρ` on `L`-valued points, its continuity
`continuousConstSMul_pointAction` and the local smallness above are supplied locally.
Worker 21's `QuasiEtaleSite.pointEquivariance L ρ h` gives the published
`TwistedOver.PointEquivariance` of the family of points.

- `quasiEtaleCompactSectionsRep L ρ h R`:
  `Sheaf (twistedQuasiEtaleTopology ρ) (ModuleCat R) ⥤ Rep R G`, the published
  `sheafCompactSectionsRep` for the quasi-étale topology of `X`. It is additive
  (`quasiEtaleCompactSectionsRep_additive`).
- `quasiEtaleCompactSectionsSmooth L ρ h R`: its smooth part, with values in
  `SmoothRep R G`. It models Berkovich's `Γ_{c,X{G}}(F) = lim_→ Γ_{c,X(N)}(F)`, as
  explained in `TwistedCompactSupport`. It is additive.
- `quasiEtaleGSheafCompactSections L ρ h R`: `Γ_{c,X{G}}` on quasi-étale `G`-sheaves,
  `QuasiEtaleGSheaf ρ (ModuleCat R) ⥤ SmoothRep R G`. It is the published
  `discreteCompactSections` for the lift system `compactLiftSystem ρ`.
  `quasiEtaleGSheafCompactSections_eq` (by `rfl`) identifies it with the inclusion into
  sheaves followed by `quasiEtaleCompactSectionsSmooth`. It is additive.

## Cohomology with compact support

The remaining hypotheses are `[Small.{w} G]` and
`[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`.
The latter is the published condition of `LocalActionDiscretePart`. Every covering
sieve of a compact quasi-étale object with a lift contains a finite family of arrows
from compact quasi-étale objects with lifts, each locally equivariant, that generates a
covering sieve. It is what makes discrete sheaves an abelian category with exact
discrete-part coreflector. Geometrically it combines the finiteness of quasi-étale
coverings of compact spaces with Berkovich's Key Lemma on lifts (compare Worker 21's
statement `QuasiEtaleActionLiftStatement`). It is not proved here.

- `quasiEtaleGSheafCompactCohomology L ρ h R q`:
  `QuasiEtaleGSheaf ρ (ModuleCat R) ⥤ SmoothRep R G`, Berkovich's `H^q_c(X{G}, F)` for
  quasi-étale `G`-sheaves. It is the published `discreteCompactDerived`, the right
  derived functors of `Γ_{c,X{G}}` computed with injective resolutions among
  quasi-étale `G`-sheaves. Sheafification and enough injectives come from the theorems
  above.
- `quasiEtaleGSheafCompactCohomologyZeroIso`: `H^0_c(X{G}, -) ≅ Γ_{c,X{G}}`.
- `isZero_quasiEtaleGSheafCompactCohomology_succ_of_injective`: `H^{q+1}_c(X{G}, F) = 0`
  for injective `F`.
- `quasiEtaleGSheafCompactComplex L ρ h R`, with `[HasDerivedCategory.{w'} (SmoothRep R G)]`:
  the complex `RΓ_c(X{G}, F)` in `DerivedCategory.Plus (SmoothRep R G)`. It is the published
  `DiscreteSheafDerivedComplex.compactComplex`. That construction needs a derived
  category of the source. Here it is Mathlib's `HasDerivedCategory.standard` for
  quasi-étale `G`-sheaves, so no hypothesis about it is needed. The value of the
  functor does not mention that choice.
- `quasiEtaleGSheafCompactComplexHomologyIso F q`: the cohomology of `RΓ_c(X{G}, F)` in
  degree `q` is `H^q_c(X{G}, F)`.
- `isZero_quasiEtaleGSheafCompactComplex_homology F hn`: no cohomology in negative degrees.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.5, printed p.11 = PDF p.11, before Corollary 1.5.2: "Let F be an étale abelian
  sheaf on X(G). The support of an element f ∈ F(X(G)) is the set
  Supp(f) = {x ∈ X | f_x ≠ 0} … The values of the high direct images of the functor
  F ↦ Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F), where N runs through open subgroups of G,
  are denoted by H^q_c(X{G}, F)."
- Definition 1.4.1, printed pp. 7–8: a quasi-étale `G`-sheaf is a quasi-étale
  `G^d`-sheaf such that for any quasi-étale `U → X` with compact `U` the action of
  `G_U` on `F(U)` is discrete; the category is `T_G(X_qét)`.
- Theorem 1.4.2, printed p.8: "The inverse image functor for the morphism
  b : X → X(G) induces an equivalence of categories X(G)~_qét ⥲ T_G(X_qét)
  (resp. X(G)~_ét ⥲ T_G(X_ét))." Corollary 1.4.3, printed p.10: for
  `F ∈ X(G)~_ét` one has `F ⥲ µ_* µ^* F`, where `µ : X(G)_qét → X(G)_ét`, so `µ^*` is
  fully faithful.

## Provenance and correspondence

This module specializes derived infrastructure. The choices below are ours:

- Berkovich defines `H^q_c(X{G}, F)` for étale abelian sheaves on `X(G)`. This module
  defines it for quasi-étale `G`-sheaves, through the twisted model of `T_G(X_qét)`. By
  Theorem 1.4.2 and Corollary 1.4.3, étale sheaves on `X(G)` embed fully faithfully into
  quasi-étale ones. The comparison between the étale and quasi-étale compactly supported
  cohomology is not formalized, nor is Theorem 1.4.2.
- Supports are taken in the `L`-valued points, with the topology induced from `|X|`, as
  in `AnalyticCompactSupport`. The same remarks on compactness and stalks apply. The
  point axioms are a hypothesis.
- The derived functors are taken in the category of quasi-étale `G`-sheaves, not in
  all sheaves on the twisted site, as in `TwistedCompactSupport`.
- The finite equivariant refinements are a hypothesis (see above). Sheafification and
  enough injectives are proved.
- Essential smallness relies on the coefficient universe `max u (v + 1) uL`, which
  contains the objects of the sites. It is the universe forced by the points.

## Not formalized here

The finite equivariant refinements, the point axioms for complete algebraically closed
`L`, the comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` of Corollary 1.5.2 on the
quasi-étale site, and the Godement resolutions and truncations of Harris §2 on this
site.
