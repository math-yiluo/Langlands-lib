# Rational-point topology of the actual smooth dimension decomposition

`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionTopologyStatement`
is a proposition interface for the topological bridge from the published
algebraic dimension decomposition to the varying-dimensional manifold assertion
of Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Proposition 5.4, printed pp.15–16. This module states the bridge and proves
nothing.

For every nontrivially normed henselian valued field `K`, every genuine
algebraic space `X` over `Spec K`, every `hX : SmoothOverBase X`, and
quasi-separatedness of `X`, the published actual-section equivalence

```text
SmoothDimensionPieces.fieldPointEquiv hX :
  RingPoints K X K ≃
    Σ n : ℕ, RingPoints K (SmoothDimensionPieces.space hX n) K
```

is a homeomorphism. The topology on `X(K)` and on each dimension piece's
`K`-points is exactly `etaleChartTopology`. The topology on the dependent sum
is Mathlib's disjoint-union topology, with each summand carrying its own
étale-chart topology. It is not a topology transported along the equivalence.
All natural-number indices are retained, including empty pieces, and there is
no finite-range or quasi-compactness hypothesis.

The equivalence and its inverse are the maps already constructed in
`SmoothSourceDimensionFieldPoints`: a section selects its intrinsic dimension
and factors through the actual represented open piece; a dependent pair maps
back by that piece's actual inclusion. The statement concerns these maps on
actual scheme-test sections, not the ordinary quotient point set. The algebraic
pieces and their restricted smooth atlases are from
`SmoothSourceDimensionPieces`, and the atlas-independent ordinary-point
dimension is from `SmoothSourcePointDimension`.

Smoothness supplies local finite type. Completeness, local separatedness,
global separatedness, and a common dimension are not assumed in this
topological bridge. The published open-immersion theorem
`isOpenEmbedding_ringPointsMap` applies to quasi-separated spaces locally of
finite type over a henselian valued field without local separatedness. Each
piece is quasi-separated by `SmoothDimensionPieces.space_isQuasiSeparated`.
This records the broader topological scope separately from the local
separatedness needed for the later full analytic local-isomorphism package.

The provenance is derived. Conrad asserts the smooth-space analytic structure
without a pure-dimension restriction on printed p.15 and constructs it from
étale scheme charts on printed p.16; he does not separately state this
dependent-sum homeomorphism. The published algebraic pieces and the
open-immersion property of the étale-chart topology motivate the exact bridge.
No analytic assembly, functoriality across target dimension pieces, étale
dimension preservation, scheme agreement, or uniqueness conclusion is asserted
by this module. Those remain later definitions, statements and proofs.

Source: registered `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.15, Proposition 5.4, smooth complete-field manifold clause, and
printed p.16, final paragraph of its proof.
