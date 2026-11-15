# Étale local analytic isomorphisms across actual dimension pieces

Author: Worker 3519.

This derived statement supports Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, December 31, 2011, printed p.15,
Proposition 5.4, and the final paragraph of its proof on printed p.16.
The registered original is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad's analytic structure carries étale maps to local analytic
isomorphisms and allows smooth components of differing dimensions. This
unit states the transfer of the pure-dimensional family's property to the
concrete varying-dimensional atlases. It contains no proof.

`SmoothSourceDimensionEtaleAnalyticIsoStatement` is a proposition
definition in `Langlands.AlgebraicGeometry.AlgebraicSpace`.
It quantifies a nontrivially normed henselian valued field `K`, a family
`σ : AnalyticPointStructure K` satisfying `σ.IsAdmissible`, actual
smooth algebraic spaces `X` and `Y` over `Spec K`, and an actual morphism
`f : X ⟶ Y`. Quasi-separatedness and local separatedness of each space are
individual hypotheses. Smoothness supplies local finite type. The additional
morphism hypothesis is `IsEtaleMorphism f`, the existing geometric predicate.
No quasi-compactness, fixed dimension, finite dimension range, nonempty
point-space, surjectivity, or completeness hypothesis is imposed.

The admissibility premise comprises analytic pure-dimensional manifold
structures, analytic functoriality, étale local analytic isomorphisms, and
agreement with affine-space coordinates. It concerns the supplied
pure-dimensional family. The conclusion instead concerns the actual
`σ.dimensionAtlas` constructions on all of `X(K)` and `Y(K)`, using their
original `RingPoints` carriers and independently defined étale-chart
topologies.

Write `F = RingPoints.map (A := K) f`, and write `A` and `B` for those two
assembled atlases. The conclusion `A.IsLocalAnalyticIso B F` has two parts.

- At every `x : RingPoints K X K`, the intrinsic dimension of `F x` in
  `Y` equals that of `x` in `X`. These are the algebraically defined
  `SmoothDimensionPieces.fieldPointDimension` values; their equality is
  asserted here, rather than assumed.
- For every such `x`, there is an open partial homeomorphism `e` between
  the original rational-point spaces with `x ∈ e.source`, whose forward
  map agrees with `F` on its entire source. The forward branch satisfies
  `A.AnalyticOn B e e.source`, and its inverse satisfies
  `B.AnalyticOn A e.symm e.target`.

Each `AnalyticOn` includes continuity on the specified subset and analytic
coordinate expressions for every source and target atlas chart, on the full
intersection of the source-chart target, the branch domain, and the
preimage of the target-chart source. In particular the inverse assertion
tests all chart intersections on `e.target`; it is not merely an inverse
set map or a topological local inverse. Dimension preservation and the
atlases' intrinsic dimension laws force intersections of incompatible
dimensions to be empty without omitting them from these predicates.

The route for a future proof first proves the geometric dimension
preservation, then restricts to corresponding actual dimension pieces.
On those pieces the supplied family's `IsEtaleLocalIso` provides analytic
local inverse branches. The genuine piece inclusions are open embeddings
on points; they lift those branches into the original point spaces.
Checking the lifted forward and inverse coordinates on every chart
intersection supplies exactly the stated conclusion.

The source's full existence theorem uses complete fields. This conditional
transfer retains the admissible family as an explicit premise and needs no
completeness once that family is supplied. It does not supply a proof of
this transfer or admissible-family existence, the separate general-morphism
functoriality bridge, scheme agreement, or uniqueness of the full
varying-dimensional structure. Those remain separate obligations.
