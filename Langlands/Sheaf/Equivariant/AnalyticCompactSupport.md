# Compactly supported sections of étale `G`-sheaves on analytic spaces

Author: Worker 26. Uses the published `Langlands.Sheaf.PointSupport` and
`Langlands.Sheaf.Equivariant.TwistedCompactSupport` (supports and compactly
supported sections for a family of points of a site, Worker 26), and
`Langlands.Sheaf.Equivariant.AnalyticGSheaves` (twisted étale site and étale
`G`-sheaves, Worker 26). From Worker 21 it uses the `L`-valued points of analytic spaces
(`Langlands.Geometry.Analytic.FieldValuedPoints`), the points of the étale
site that they define (`EtaleGeometricPoints`), the action of `G` on them
(`EtaleGeometricPointEquivariance`) and the étale site `EtaleSite`.

## Purpose

Let a group `G` act on a `K`-analytic space `X`. Berkovich defines the
compactly supported sections of an étale sheaf through the supports of its
sections, which are subsets of the topological space `|X|`. The published
`TwistedCompactSupport` defines compactly supported global sections on a
twisted site for any family of points of the site, indexed by a topological
space with a compatible action of `G`. This module supplies those data for the
étale site of an analytic space, with the `L`-valued points of `X` as index set,
and specializes the construction. It defines

- the topology on the `L`-valued points of `X` induced from `|X|`, and proves
  that `G` acts on it by homeomorphisms;
- the comparison of compactness in this topology with compactness in `|X|`;
- the compactly supported global sections of sheaves on the twisted étale
  site, as representations of `G`, and their smooth part, Berkovich's
  `Γ_{c,X{G}}`, also on étale `G`-sheaves.

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field and `X` an object of
  Worker 21's `LocalizedCategory.{u, v, v} (K := K)` of `K`-analytic spaces.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`. Write
  `P = localizedFieldPointFunctor L`, so that `P.obj X` is the type of
  `L`-valued points of `X`, and `|X| = localizedSpaceFunctor.obj X`.
- `G : Type z` is a group and `ρ : G →* Aut X`. The smooth parts use
  `[TopologicalSpace G] [IsTopologicalGroup G]`.
- `h : ∀ x : P.obj X, EtaleSite.PointAxioms L x`: every `L`-valued point
  satisfies Worker 21's point axioms. This is a hypothesis of the
  constructions below. Worker 21's separate statement module
  `EtaleGeometricPointStatement` asserts it for complete algebraically closed
  `L`; it is not used here.
- Coefficients: `R : Type (max u (v + 1) uL)` is a commutative ring and sheaves
  take values in `ModuleCat.{max u (v + 1) uL} R`. This is the universe of the
  points `EtaleSite.toPoint L x (h x)`, which the published construction
  requires to equal the universe of the modules.

## Topology on the `L`-valued points

- `pointProjection L X : P.obj X → |X|` sends an `L`-valued point to its
  underlying point. It is the component at `X` of Worker 21's natural map
  `localizedFieldPointProjection L`, with the `ULift` removed.
- `pointTopology L X` is the topology on `P.obj X` induced by
  `pointProjection L X` (an `abbrev`, not a global instance, since `P.obj X`
  is a type of the Library on which other topologies could be wanted).
  `isInducing_pointProjection` records that the projection is inducing.
- `pointProjection_map L f x`: the underlying point of `P.map f x` is the image
  of the underlying point of `x` under the continuous map of `f`. This is the
  naturality of `localizedFieldPointProjection L`.
- `exists_isCompact_superset_iff L S`: a set `S` of `L`-valued points lies in
  a compact subset of `P.obj X` exactly when there is a compact `C ⊆ |X|` with
  `C ⊆ range (pointProjection L X)` and `pointProjection L X '' S ⊆ C`. One
  direction takes images under the continuous projection. The other takes the
  preimage of `C`, which is compact because the projection is inducing and `C`
  lies in its range (Mathlib's `IsInducing.isCompact_preimage'`).
- `exists_isCompact_superset_iff_of_surjective L hX S`: if every point of
  `|X|` underlies an `L`-valued point, the range condition disappears: `S`
  lies in a compact set exactly when its image lies in a compact subset of
  `|X|`.
- `continuousConstSMul_pointAction L ρ`: with `pointTopology L X` and
  Worker 21's action `EtaleSite.pointAction L ρ` (`g • x = P.map (ρ g).hom x`),
  each `g` acts continuously. By `pointProjection_map`, the projection of
  `g • x` is the image of the projection of `x` under the homeomorphism of `|X|`
  given by `ρ g`, and a map into an induced topology is continuous when its
  composite with the inducing map is.

## Local smallness of the étale site

- `etaleSite_locallySmall X` (instance): the morphisms of `EtaleSite X` form
  types equivalent to types in `Type (max u v)`. The forgetful functor to
  `LocalizedCategory` is faithful, so Mathlib's `locallySmall_of_faithful`
  applies.
- `etaleSite_locallySmall_points X`: local smallness in the universe
  `max u (v + 1) uL` of the points, by lifting (Mathlib's `small_lift`). It is a
  theorem rather than an instance, because the universe `uL` does not occur in
  `EtaleSite X` and could not be inferred. The definitions below supply it
  locally with `haveI`.

## Supports

- `etalePoints L h x`, for an `L`-valued point `x`, is Worker 21's point
  `EtaleSite.toPoint L x (h x)` of the étale topology, in universe
  `max u (v + 1) uL`. Its fibre over an étale `U → X` is the set of
  `L`-valued points of `U` over `x`.
- `isCompactlySupported_etalePoints_iff L h s`: for a presheaf `F` of modules on
  `EtaleSite X`, an object `U` and `s ∈ F(U)`, the section `s` is compactly
  supported for the family `etalePoints L h` with the topology `pointTopology`
  (the published `PointSupport.IsCompactlySupported`) exactly when the image of
  its support (the published `PointSupport.support`) in `|X|` lies in a compact
  subset of `|X|` made of underlying points of `L`-valued points. The support of
  `s` is the set of `L`-valued points `x` of `X` such that the germ of `s` at some
  `L`-valued point of `U` over `x` is nonzero. The statement is
  `exists_isCompact_superset_iff` applied to this set.

## Compactly supported sections on the twisted étale site

In all the following, the topology `pointTopology L X`, the action
`EtaleSite.pointAction L ρ`, its continuity `continuousConstSMul_pointAction`
and the local smallness `etaleSite_locallySmall_points` are supplied locally.
The family of points is `etalePoints L h`, and Worker 21's
`EtaleSite.pointEquivariance L ρ h` supplies the published
`TwistedOver.PointEquivariance` (the fibre of `gU` at `g • x` is identified
with the fibre of `U` at `x`).

- `etaleCompactSectionsRep L ρ h R`:
  `Sheaf (twistedEtaleTopology ρ) (ModuleCat R) ⥤ Rep R G`. It is the published
  `sheafCompactSectionsRep` for the étale topology of `X`. A sheaf `F` on the
  twisted étale site goes to its compactly supported global sections, that is,
  the sections over `X` (the identity of `X`) of the restriction of `F` to
  `EtaleSite X` whose support lies in a compact subset of the `L`-valued points.
  `G` acts by the published action of the twisted site.
  `etaleCompactSectionsRep_additive` is the additivity instance.
- `etaleCompactSectionsSmooth L ρ h R`: its composite with the smooth part
  functor `SmoothRep.smoothPartFunctor R G`, with values in smooth
  representations. This models Berkovich's
  `Γ_{c,X{G}}(F) = lim_→ Γ_{c,X(N)}(F)` over open subgroups `N`, as explained
  in `TwistedCompactSupport`. `etaleCompactSectionsSmooth_additive` is the
  additivity instance.
- `etaleGSheafCompactSections L ρ h R`: the restriction of
  `etaleCompactSectionsSmooth` to the étale `G`-sheaves
  `EtaleGSheaf ρ (ModuleCat R)` of `AnalyticGSheaves`, through the inclusion
  `smoothSheafInclusion` of the lift system `distinguishedLiftSystem ρ`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.5, printed p.11 = PDF p.11, before Corollary 1.5.2:

> Let F be an étale abelian sheaf on X(G). The support of an element
> f ∈ F(X(G)) is the set Supp(f) = {x ∈ X | f_x ≠ 0}, where f_x is the image
> of f in F_x. It is a closed subset of X. The values of the high direct images
> of the functor F ↦ Γ_{c,X(G)}(F) := {f ∈ F(X(G)) | Supp(f) is compact} are
> called the cohomology groups with compact support and denoted by
> H^q_c(X(G), F). The values of the high direct images of the functor
> F ↦ Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F), where N runs through open
> subgroups of G, are denoted by H^q_c(X{G}, F).

The stalks `F_x` are those of Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, §4.2, printed p.87, where `F_x` is a discrete
`G_ℋ(x)`-set. Worker 21's `EtaleGeometricPoints` quotes that passage, reads the
underlying set of `F_x` as the stalk at a geometric point over `x`, and models
geometric points as `L`-valued points.

## Provenance and correspondence

This module specializes derived infrastructure. The choices below are ours:

- Berkovich's support is a subset of `|X|`, made of the points at which the
  stalk of `f` is nonzero. The published construction takes supports in the
  index set of a family of points. Here the index set is the set of `L`-valued
  points, with the topology induced from `|X|`. The support of a section is then
  a set of `L`-valued points, and its image in `|X|` is the set of underlying
  points of `L`-valued points at which some germ of the section is nonzero.
- Compactness. Berkovich asks that `Supp(f)` be compact. The published notion
  asks that the support lie in a compact set. By
  `exists_isCompact_superset_iff_of_surjective`, when every point of `|X|`
  underlies an `L`-valued point, this means that the image of the support in
  `|X|` lies in a compact subset of `|X|`. For a closed support in a Hausdorff
  space this is compactness of the support. This module proves neither the
  surjectivity, nor the closedness of supports, nor that the stalks at
  `L`-valued points over `x` are Berkovich's stalk `F_x`.
- The point axioms `h` are a hypothesis, as in Worker 21's
  `EtaleSite.pointEquivariance`.
- `Γ_{c,X{G}}` is the smooth part of the compactly supported global sections,
  as in `TwistedCompactSupport`. Sheaves on the twisted étale site model
  Berkovich's étale `G^d`-sheaves (`TwistedOver`), and `EtaleGSheaf` models his
  étale `G`-sheaves (`AnalyticGSheaves`).

## Not formalized here

The derived functors `H^q_c(X{G}, F)` are not defined in this module. The
published `TwistedCompactSupport` takes derived functors in the category of
discrete sheaves of a local action system, which needs finite equivariant
refinements of coverings of admissible objects. The admissible objects of
`distinguishedLiftSystem ρ` need not be compact, so that hypothesis can fail
for the twisted étale site, and the étale `G`-sheaves `EtaleGSheaf` are not
known to form an abelian category with enough injectives. Berkovich's
quasi-étale `G`-sheaves (`QuasiEtaleGSheaf`) are discrete sheaves for the
compact quasi-étale objects; their compactly supported cohomology needs points
of the quasi-étale site, which are not available in the Library.
