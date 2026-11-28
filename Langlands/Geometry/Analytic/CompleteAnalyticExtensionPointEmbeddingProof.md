# Proof of the analytic comparison for extension of rational points

The theorem `completeAnalyticExtensionPointEmbedding` in the namespace
`Langlands.Analytic.SpaceAnalytification` proves
`CompleteAnalyticExtensionPointEmbeddingStatement.{u}` for every universe
\(u\). The same module proves
`henselianExtensionPointEmbedding_of_analytification`. It derives
`HenselianExtensionPointEmbeddingStatement.{u}` from
`SpaceAnalytificationExistenceStatement.{u}` and
`SpaceAnalytificationGroundFieldStatement.{u}`. Both theorems use only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The argument is the last paragraph of the proof of Proposition 5.11(3),
printed p. 19, of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
Analytification is compatible with ground field extension. So the injection
\(X(k) \to X(k')\) is identified with \(X^{an}(k) \to (X^{an})_{k'}(k')\),
which is a closed embedding on the constituents of an affinoid covering of
\(X^{an}\). In the Lean proof, the identification is the projection
identity below. The rational-point topology comparison gives the embedding,
and the closed rational locus of the scalar-extended atlas gives
closedness.

## Notation

Let \(L/K\) be an isometric extension of complete nontrivially normed
ultrametric fields, of any degree. Let \(X\) be a separated algebraic space
locally of finite type over \(K\), and \((Y,p)\) an analytification of \(X\)
(`IsAnalytification K X Y p`). Write \(X_L\) for
`baseChange (Spec.algebraMap K L) X` and \(Y_L\) for
`(localizedFunctor K L).obj Y`. Write \(\pi : Y_L \to Y\) for the underlying
continuous map of `(localizedProjection K L).app Y`, and
\(x \mapsto x_L\) for `extensionPointMap L X`. For a presentation \(P\) of
\(K\), `rationalPoint p P x` applies the analytic map `p K P x` of the test
point \(x : \operatorname{Spec} K \to X\) to the analytic point of the
identity character of \(K\).

## The projection identity

The private lemma `projection_rationalPoint_extension` applies the
ground-field hypothesis to \((Y,p)\). It obtains a test-point family \(q\)
making \(Y_L\) an analytification of \(X_L\), and proves
\(\pi(\texttt{rationalPoint}\ q\ Q\ x_L) = \texttt{rationalPoint}\ p\ P\ x\)
for all presentations \(P\) of \(K\) and \(Q\) of \(L\) and all
\(x \in X(K)\).

The proof specializes the ground-field comparison to the affine test
\(A = K\) with presentation \(P\). Write \(T = L \otimes_K K\), \(R\) for
`baseChangePresentation K L P` and \(x_T\) for the \(T\)-point of \(X_L\)
corresponding to \(x\) under `baseChangeRingPointsEquiv`. The comparison
gives an isomorphism \(c\) from the scalar extension of
`localized K P` to `localized L R`. Along \(c^{-1}\), the projection
becomes `baseChangeMap K L P`. The analytic map \(q_{T,R}(x_T)\) of the
test point \(x_T\) satisfies \(q_{T,R}(x_T) \circ c = (p_{K,P}(x))_L\).

Let \(\varphi = \) `rationalLift K L idK` be the \(L\)-algebra character
\(T \to L\) that extends the identity character of \(K\). Its composite with
\(a \mapsto 1 \otimes a\) is the algebra map \(K \to L\)
(`rationalLift_tmul`). By `baseChangeRingPointsEquiv_changeRing` and
`RingPoints.changeRing_comp`, changing \(x_T\) along \(\varphi\) gives
\(x_L\). The naturality of \(q\) along \(\varphi\) then rewrites the analytic
point of \(x_L\). So does `affineAnalytificationRationalPointNaturality`,
which sends the analytic point of the identity character of \(L\) to the
analytic point \(z\) of \(\varphi\). The result is
\[
  \texttt{rationalPoint}\ q\ Q\ x_L = (p_{K,P}(x))_L\bigl(c^{-1}(z)\bigr).
\]
Naturality of `localizedProjection` along \(p_{K,P}(x)\) moves \(\pi\) to the
affine test. There \(c^{-1}(z)\) projects to `baseChangeMap K L P z`. By
`baseChangeMap_analyticPoint`, this is the analytic point of the identity
character of \(K\). This proves the identity.

## Embedding

The main theorem takes the family \(q\) of the lemma and fixes the
presentations \(P\) = `FinitePolynomialPresentation.ofFiniteType K K` and
\(Q\) = `FinitePolynomialPresentation.ofFiniteType L L`. The space \(X_L\)
is separated and locally of finite type (`IsSeparated.baseChange`, and
`HasAtlasProperty.baseChange` for `LocallyOfFiniteTypeOverBase`). So
`spaceAnalytificationRationalPoints`
shows that \(g = \) `rationalPoint q Q` and `rationalPoint p P` are
topological embeddings for the étale-chart topologies. The map
\(x \mapsto x_L\) is continuous (`continuous_extensionPointMap`). Its
composite with the continuous map \(\pi \circ g\) is the embedding
`rationalPoint p P`, by the projection identity. Hence \(x \mapsto x_L\) is
an embedding (`IsEmbedding.of_comp`).

## Closed range

Write \(Y\) as `localizedObjectEquiv A` for a saturated atlas presentation
\(A\). By construction of `localizedFunctor`, \(Y_L\) is the saturation of
the scalar-extended affinoid atlas
\(A_L\) = `IndexedAffinoidAtlas.GroundFieldExtension.presentation K L
A.presentation.atlas`. Let \(S\) be the \(K\)-rational locus of \(A\) and \(R'\)
the \(L\)-rational locus of \(A_L\).

* The private lemma `range_rationalPoint` uses the field-point bijection of
  `spaceAnalytificationFieldPoints`. It shows that the range of
  `rationalPoint p P` is the \(K\)-rational locus of the presentation
  underlying \(Y\), here \(S\). Applied over \(L\), it gives that the range
  of \(g\) is the rational locus of the saturation of \(A_L\). The private
  lemma `rationalLocus_saturation` identifies this with \(R'\), by
  `FieldPointSaturationComparison.saturationEquiv`.
* `IndexedAffinoidAtlas.GroundFieldExtension.groundFieldRationalLocus`
  shows two things. The points of \(R'\) that project into \(S\) form a
  closed subset of \(R'\), and \(\pi\) is injective on
  \(R' \cap \pi^{-1}(S)\). That theorem is stated for the atlas projection
  `IndexedAffinoidAtlas.GroundFieldExtension.projection K L
  A.presentation.atlas`; on underlying points, \(\pi\) unfolds
  definitionally to it.
* Let \(g_R : X_L(L) \to R'\) be the corestriction of \(g\). It is continuous.
  The range of \(x \mapsto x_L\) is the preimage under \(g_R\) of that closed
  subset. Points \(x_L\) lie in it by the projection identity. Conversely, let
  \(\pi(g(y)) \in S\). Then \(\pi(g(y)) = \texttt{rationalPoint}\ p\ P\ x\)
  for some \(x \in X(K)\). This also equals \(\pi(g(x_L))\), so injectivity
  of \(\pi\) gives \(g(y) = g(x_L)\). Injectivity of \(g\) gives
  \(y = x_L\).

So the range is closed, and with the embedding,
\(x \mapsto x_L\) is a closed embedding.

## The derived henselian theorem

`henselianExtensionPointEmbedding_of_analytification` applies
`ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete`.
That reduction uses completions and separated open subspaces. It needs the
closed-range assertion `CompleteExtensionPointClosedRangeStatement` for
complete fields \(K \subseteq L\) and separated \(X\). If the norm of \(K\)
is ultrametric, the norm of \(L\) is ultrametric as well
(`IsUltrametricDist.of_normedAlgebra`). In that case,
`SpaceAnalytificationExistenceStatement` gives an analytification of \(X\),
and `completeAnalyticExtensionPointEmbedding` with the ground-field
hypothesis gives the closed range. Otherwise the theorem uses the Library
proof `CompleteExtensionClosedRange.completeExtensionPointClosedRange`,
which covers all complete fields.

The Library also proves `HenselianExtensionPointEmbeddingStatement` without
hypotheses, as `henselianExtensionPointEmbedding` in the module
`HenselianExtensionPointEmbeddingProof`. The theorem here records Conrad's
analytic route for the nonarchimedean closed-range input.
