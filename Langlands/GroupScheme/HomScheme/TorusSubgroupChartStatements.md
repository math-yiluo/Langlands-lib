# Chart covers of the functor of closed torus subgroups

Author: Worker 1421.

This module states four propositions in namespace
`Langlands.GroupScheme.TorusSubgroupModuli`. They split the proof of
`SmoothTorusSubgroupRepresentabilityStatement` into three independent steps. The
module proves none of them and assumes no representability. The predicates
`IsOpenChart` and `CoversFieldPoints` come from the companion module
`Langlands.GroupScheme.HomScheme.TorusSubgroupCharts`.

A chart cover of an actual group scheme `G/S` has four parts: an index type
`ι : Type u`, objects `U k : Over S`, actual group schemes `K k` over
`(U k).left`, and actual homomorphisms
`j k : K k ⟶ (GroupScheme.baseChange (U k).hom).obj G`. Every `j k` must
satisfy `IsOpenChart`, and the family must satisfy `CoversFieldPoints`.

## `ChartCoverStatement`

Let `S : Scheme.{u}` be arbitrary and `G : GroupScheme S` an actual group
scheme with `G.X.hom` smooth and affine (instance arguments `Smooth G.X.hom`
and `IsAffineHom G.X.hom`). Then `G` has a chart cover.

## `FiniteTypeChartCoverStatement`

The same conclusion when `S` is `Spec (CommRingCat.of R)`, for a commutative
ring `R : Type u` that is a finitely generated algebra over `ℤ`
(`Algebra.FiniteType ℤ R`). The group `G` is again an actual smooth affine
group scheme over this base.

## `ChartGluingStatement`

`ChartCoverStatement.{u} → SmoothTorusSubgroupRepresentabilityStatement.{u}`.
This is the gluing step. The intended proof glues the charts with Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` (Stacks Project,
Tag 01JJ). It applies this to the Zariski sheaf on `Sch` whose value at `T`
is the set of pairs `(t : T ⟶ S, admissible subgroup functor of G_t)`. The
universal family is the representative of the universal element. Smoothness of
the glued scheme follows from smoothness of the charts.

## `ChartCoverReductionStatement`

`FiniteTypeChartCoverStatement.{u} → ChartCoverStatement.{u}`. This is the
noetherian reduction. Its intended proof restricts `G` to affine opens
`Spec A` of `S` and writes each restriction as the base change of a smooth
affine group scheme over a finitely generated `ℤ`-subalgebra of `A` (EGA IV 8).
It then pulls charts back along both base changes and uses that field points of
`S` factor through affine opens.

## Truth and provenance

Each proposition is a consequence of the torus case of SGA 3, Exposé XI,
Theorem 4.1 (registered source `sga3-exposes-xi-xii-xiv-gille-polo-2008`,
`Expo11.pdf`, PDF page 20, recomposed page 104, original page 157). If a
smooth moduli scheme `M` with universal family `j` exists, then the single
family `j` is a chart cover: `injective` and `isOpen` (with `V` the whole test
scheme) follow from universality, and `CoversFieldPoints` holds by
universality at field points. The two implications are therefore
consequences of true propositions. The proof of Theorem 4.1, on PDF pages
21-22, begins with the same reduction to a noetherian base, by EGA IV 8. It
then covers the functor by representable open subfunctors using
Propositions XI 3.5 and 3.7 (PDF pages 12-17). These four propositions are the
Lean interfaces for that reduction and for that covering. They are internal
statements of this project, not literal statements of the source.
