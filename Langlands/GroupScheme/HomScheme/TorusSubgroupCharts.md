# Open charts of the functor of closed torus subgroups

Author: Worker 1421.

This module defines the chart interface used to build the smooth moduli
scheme of `TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement`.
It defines two predicates, `IsOpenChart` and `CoversFieldPoints`, in namespace
`Langlands.GroupScheme.TorusSubgroupModuli`. It proves nothing and assumes no
representability. The propositions that use these predicates are in the
companion module `Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements`.

Throughout, `S : Scheme.{u}` is arbitrary and `G : GroupScheme S` is an actual
group scheme. For `T : Over S`, the group `G_T` is
`(GroupScheme.baseChange T.hom).obj G`. A family over `U : Over S` is an
actual homomorphism `j : K ⟶ G_U` with `K : GroupScheme U.left`. Its value
at `a : T ⟶ U` is the Library evaluation `TorusSubgroupModuli.evaluate j a`:
the literal range in `G_T` of the pulled-back inclusion, followed by the
ambient pullback comparison.

Write `F` for the functor that sends `T/S` to the set of admissible subgroup
functors of `G_T` (`TorusSubgroupModuli.IsAdmissible`, an actual closed
relative torus). A family `j` gives a transformation from the functor of
points of `U` to `F`, namely `a ↦ evaluate j a`.

## `IsOpenChart j`

`IsOpenChart j` is a structure with five fields:

- `isClosedSubgroup`: `j` is a closed subgroup inclusion (`IsClosedSubgroup j`).
- `isTorus`: `K` is a relative torus (`RelativeTorus.IsTorus K`).
- `smooth`: `U.hom` is smooth.
- `injective`: two parameters `a b : T ⟶ U` over any `T/S` with the same
  evaluation are equal.
- `isOpen`: take any `T/S` and any actual closed torus inclusion
  `i : L ⟶ G_T`. Then there is an open `V` of `T.left` with the following
  property. For every `T'/S` and every `b : T' ⟶ T` over `S`, some parameter
  `a : T' ⟶ U` satisfies `evaluate j a = evaluate i b` exactly when the image
  of `b.left` lies in `V`.

The last two fields say that `a ↦ evaluate j a` is relatively representable by
open immersions. The fibre product of this transformation with the
transformation from `T` defined by `i` is the subfunctor of `T` of all `b` in
the displayed set. The field `isOpen` says that this subfunctor is the functor
of points of the open subscheme `V`. The field `injective` makes the
corresponding `a` unique. This is the notion of relatively representable open
immersion of Stacks Project, Tag 01JJ, written for the subgroup functor `F`.
The rendered Mathlib analogue is
`AlgebraicGeometry.IsOpenImmersion.presheaf`. The closed torus inclusions `i`
range over all of `F(T)`, because every admissible subgroup functor has such a
representative.

## `CoversFieldPoints j`

Let `ι : Type u` index a family of families `j k : K k ⟶ G_{U k}`.
`CoversFieldPoints j` says the following. Take any field `F : Type u`, any
morphism `x : Spec F ⟶ S` and any actual closed torus inclusion
`i : L ⟶ G_x`. Then some member `k` and some parameter
`a : Over.mk x ⟶ U k` satisfy `evaluate (j k) a = SubgroupFunctor.range i`.
Combined with the field `isOpen`, this gives joint local surjectivity of the
charts on every `T/S`. A point `t` of `T` and the residue-field point at `t`
yield such data, so `t` lies in the open `V` of some chart.

## Provenance

These are internal definitions on the way to the torus case of SGA 3,
Exposé XI, Theorem 4.1 (registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 20,
recomposed page 104). The proof there, on PDF pages 21-22, reduces to a
noetherian base. It then covers the functor by representable subfunctors,
using Proposition XI 3.7 (PDF pages 13-17) and Proposition XI 3.5 (PDF
pages 12-13). A chart
in the sense of `IsOpenChart` is a representable open subfunctor of this kind,
with a smooth representing scheme. `CoversFieldPoints` is the joint
surjectivity of such a family on field-valued points. The open-immersion
notion follows Stacks Project, Tag 01JJ, and Mathlib's
`AlgebraicGeometry.IsOpenImmersion.presheaf`.
