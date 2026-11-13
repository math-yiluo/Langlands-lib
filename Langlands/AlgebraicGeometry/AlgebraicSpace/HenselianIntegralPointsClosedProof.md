# Integral points over a henselian valuation ring: closedness

Authors: Worker 80 of the previous project instance (proof draft, shared as the draft of Task 5692),
Worker 50 (check, removal of one redundant line, and submission).

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsClosedStatement.{u}`,
the closedness part of Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.16–17, in the corrected scope of the published
statement. The entry theorem is `henselianIntegralPointsClosed`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a subring
`O`, with `HenselianLocalRing O`, and let `X` be a separated algebraic space over `Spec O`. For
`ι : X(O) → X_K(K)`, `x ↦ (baseChangeRingPointsEquiv O K K X).symm
(RingPoints.changeRing (Algebra.ofId O K) x)`, the map `ι` is injective, and if
`FiniteTypeOverRing O X` its range is closed for `etaleChartTopology K X_K`.

## Route used

The statement program Task 5218 (`5e83271c-c91b-45ad-b94a-ea03601fec06`) proposed Nagata
compactification for algebraic spaces with the valuative criterion, and allowed any correct
route. This proof uses neither. It combines two published intermediate statements, each proved in
its own module:

- `UniformFieldPointChartsStatement` (proof `uniformFieldPointCharts`, module
  `UniformFieldPointChartsProof`): a separated, quasi-compact space has finitely many affine
  étale charts through which every field-valued point lifts. This is the construction of
  Stacks Project Tag 0BBN (symmetric quotients of distinct related tuples) with Galois descent.
- `HenselianChartIntegralPointsClosedStatement` (proof `henselianChartIntegralPointsClosed`,
  module `HenselianChartIntegralPointsClosedProof`): for one affine étale chart `U → X` of a
  separated space locally of finite type, the image of `U(O)` in `X_K(K)` is closed. The
  integral points form a closed bounded set of `U_K(K)`, and the Library theorem
  `isClosed_preimage_image_of_bounded` controls its image in other charts.

Hensel's lemma (`HenselianIntegralPointsCompact.exists_point_of_residue_point`) connects the
two: an `O`-point whose residue point lifts to a chart lifts to that chart.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `henselianIntegralPointsClosed_of_charts (hF : UniformFieldPointChartsStatement.{u})
  (hC : HenselianChartIntegralPointsClosedStatement.{u}) :
  HenselianIntegralPointsClosedStatement.{u}`.
- `henselianIntegralPointsClosed : HenselianIntegralPointsClosedStatement.{u}`, the reduction
  applied to `uniformFieldPointCharts` and `henselianChartIntegralPointsClosed`.

## Proof of `henselianIntegralPointsClosed_of_charts`

1. Injectivity: `RelativeIntegralPoints.changeRing_injective` for the injective inclusion
   `O → K`, composed with the bijection `(baseChangeRingPointsEquiv O K K X).symm`. This is the
   argument of the Library proof `henselianIntegralPointsClosedOfLocallyCompact`.
2. Assume `FiniteTypeOverRing O X`. Its atlas is locally of finite type, so
   `LocallyOfFiniteTypeOverBase X`; its source is quasi-compact over the affine `Spec O`, hence
   compact (`QuasiCompact.compactSpace_of_compactSpace`), so `IsQuasiCompact X`.
3. `hF` gives affine schemes `U i` (`i : Fin n`) and étale `f i : U i → X` through which every
   field-valued point lifts. Let `N i` be the image of `U i (O)` in `X_K(K)`, the set in `hC`.
4. `range ι = ⋃ i, N i`. Each `N i` lies in the range. Conversely, for `x ∈ X(O)`, its residue
   point in `X(κ)`, `κ` the residue field of `O`, lifts to a `κ`-point of some `U i` by `hF`,
   and `exists_point_of_residue_point` lifts `x` to an `O`-point of `U i`.
5. Each `N i` is closed by `hC`, and a finite union of closed sets is closed
   (`isClosed_iUnion_of_finite`).

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7 and its
  proof, printed pp.16–17. Conrad's closedness argument uses one cover with `U(R) → X(R)`
  surjective and the identity "the full preimage of `X(k) − X(R)` is `U(k) − U(R)`", which fails
  in general; the published statement's Markdown records the corrected scope. The route here
  replaces that identity by the two intermediate statements above.
