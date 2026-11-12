# Rational points of separated algebraic spaces of finite type are second countable

Author: Worker 105.

This module supplies the local input for the countable base in Conrad's p.17 claims. The source
is Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.17:
adelic points of separated algebraic spaces of finite type over the `S`-integers are second
countable. The claim is part of `Langlands.Global.AdelicSpacePointTopologyStatement`. The
module proves the corresponding fact for the local factors.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartSecondCountable`.

- `openChart`, `openChartι`: an open of an atlas scheme, as a scheme over `Spec k`, and its
  inclusion.
- `exists_lift`: let `a₀ : h_U → X` be an étale surjective atlas, and `𝒪` a family of opens
  covering `U`. Then every `k`-point of `X` lifts, over some finite separable extension `L/k`,
  to an `L`-point of one of the opens.
  - The pullback of the atlas along the point is a nonempty étale `k`-scheme. It has an `L`-point
    (`GaloisChartPoint.exists_separable_point`).
  - Its image in `U` lies in some open of `𝒪`.
- `exists_point_of_invariant`: a Galois-invariant `K`-point of an affine chart over a `k`-point
  `x` descends to a `k`-point of the chart with image `x`
  (`GaloisChartPoint.exists_desc_of_galois_invariant`, `GaloisChartPoint.changeRing_injective`).
- `exists_countable_charts`: let `X` be separated of finite type over a field `k` with a
  countable Galois family (`HasCountableGaloisFamily`). Then `X` has countably many affine
  étale charts whose `k`-points cover `X(k)`.
  - The atlas of finite type is quasi-compact, so finitely many affine opens `V` cover it.
  - For each `V` and each member `L` of the family there is one chart
    (`UniformGaloisChart.exists_chart`).
  - A point lifts over some finite separable `E`, and `E` embeds into some `L`.
- `secondCountableTopology_range`: the image of a second countable space under a continuous open
  map is second countable (`IsOpenQuotientMap.secondCountableTopology`).
- `secondCountableTopology_etaleChartTopology`: **second countability**. Let `K` be a henselian
  valued field with a countable base and a countable Galois family, and `X` separated of finite
  type over `K`. Then `etaleChartTopology K X` is second countable.
  - The chart images are open (`EtaleFiniteTypeChart.isOpenMap_pointMap`).
  - They are second countable, since the chart points are (`schemePointSecondCountability`).
  - Countably many of them cover `X(K)`
    (`TopologicalSpace.secondCountableTopology_of_countable_cover`).
