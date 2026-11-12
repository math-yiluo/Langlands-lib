# Integral points of one affine étale chart have closed image

Author: Worker 80.

`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianChartIntegralPointsClosedStatement` is an
intermediate statement for the closedness part of Corollary 5.7 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed pp.16–17. The module
only states it and contains no proof.

## The statement

Let `K : Type u` be a nontrivially normed field whose closed unit ball is a subring `O`
(`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`), and assume `O` is a henselian local ring (`HenselianLocalRing O`).
Let `X` be an algebraic space over `Spec O` that is separated (`IsSeparated X`) and locally of
finite type over the base (`LocallyOfFiniteTypeOverBase X`). Let `U` be a scheme over `Spec O`
whose underlying scheme `U.left` is affine, and let `f : U → X` be a morphism of algebraic
spaces (from the space represented by `U`) that is étale (`IsEtale (hom f)`).

Consider the map from the `O`-points of `U` to the rational points of the generic fibre
`X_K = baseChange (Spec.algebraMap O K) X`: an `O`-point `u : RingPoint O U O` is sent to the
`O`-point `f(u)` of `X` (`RingPoints.map f`, after `schemeRingPointsEquiv`), then to a
`K`-point of `X` (`RingPoints.changeRing (Algebra.ofId O K)`), then to a `K`-point of `X_K`
(`(baseChangeRingPointsEquiv O K K X).symm`). The statement says that the image of this map is
closed for the étale-chart topology `etaleChartTopology K X_K`.

## Relation to the source and derived content

Conrad's Corollary 5.7 (registered source `conrad-2011-weil-grothendieck-adelic-points`,
printed p.16) asserts that `X(R)` is open and closed in `X(k)`. For closedness, his proof
(printed pp.16–17) takes an étale scheme cover `U → X` with `U(R) → X(R)` and `U(k) → X(k)`
surjective and argues: "The full preimage of `X(k) − X(R)` in `U(k)` is `U(k) − U(R)`, which is
open in `U(k)`, so since `U(k) → X(k)` is a continuous surjective open map it follows that
`X(k) − X(R)` is open in `X(k)`."

The published statement `HenselianIntegralPointsClosedStatement` corrects the scope of that
claim to separated spaces of finite type (see its Markdown for the published
counterexamples). The present statement is the derived single-chart step of a proof in that
scope: for one affine étale chart `U` of a separated space, the image of `U(O)` is closed. It
is not stated in the source. The intended reason is that `U(O)` is a closed and bounded subset
of `U_K(K)`, and in a separated space over a henselian field the image of such a set under an
affine étale chart meets every other affine chart in a closed set (compare the Library theorem
`isClosed_preimage_image_of_bounded`). Together with finitely many charts through which every
`O`-point lifts, this gives the closedness of the image of `X(O)` when `X` is separated and of
finite type. The formulation with one affine chart, the hypotheses (separated, locally of
finite type) and the name of the statement are chosen here.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7 and its
  proof, printed pp.16–17.
