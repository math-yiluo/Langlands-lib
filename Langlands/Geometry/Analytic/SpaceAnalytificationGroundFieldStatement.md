# Ground field extension of an algebraic-space analytification

Let \(K \to L\) be an isometric extension of complete nontrivially
valued ultrametric fields, of arbitrary degree. Let \(X\) be a
separated algebraic space locally of finite type over \(K\), and let
\((Y,p)\) be an analytification in the sense of `IsAnalytification`.
The scalar extension uses the actual functor `localizedFunctor K L`.

`SpaceAnalytificationGroundFieldStatement` asserts that \(Y_L\)
admits a test-point family making it an analytification of the
algebraic base change \(X_L\). For every finitely presented affine
test with chosen polynomial presentation of \(A\), it gives an
analytic isomorphism from the scalar extension of
\((\operatorname{Spec} A)^\mathrm{an}\) to
\((\operatorname{Spec}(L\otimes_K A))^\mathrm{an}\). This isomorphism
identifies the continuous scalar projection with the restriction of
seminorms along \(a\mapsto 1\otimes a\). It identifies the
scalar-extended analytic map of each affine test point with the
analytic map of the actual base-changed test point. The isomorphism
for a given presentation works for all test points with that
presentation.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces*,
define analytification by the representable étale quotient of an étale
scheme chart in Definition 2.2.2, printed p. 7. Their Theorems 2.2.3
(printed pp. 7–8) and 2.3.5 (printed p. 13) give its functoriality and
compatibility with ground field extension. The proposition expresses
that comparison on objects and affine test maps using the Library's
`PointFamily` and `IsAnalytification`, with the affine base change
\(\operatorname{Spec}(L\otimes_K A)\). Source
`conrad-temkin-2009-nonarchimedean-analytification`, SHA-256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad uses this comparison for extension of rational points in the
proof of Proposition 5.11(3), p. 19, in
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
