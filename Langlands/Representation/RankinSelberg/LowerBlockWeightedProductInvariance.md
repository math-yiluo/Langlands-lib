# Invariance of the determinant-weighted lower-block product

This internal helper proves invariance of the exact parameter measure used in
lower-block quotient disintegration. It does not construct the block
homeomorphism, prove chart conullness, or compare this measure with a quotient
measure. Those remain separate steps of the disintegration proof.

Fix a prime `p`, an algebraic p-adic field `F : PadicField.{uF} p`, supplied
topological data `T`, and natural ranks `a,d`, including zero. Write `B_a` and
`B_d` for the actual published lower triangular subgroups and write `M` for
`Matrix (Fin d) (Fin a) F.Carrier`. The topology is `T.topology`. The scalar
field has its Borel measurable space; matrices retain their finite product
measurable space. Each triangular subgroup may have any measurable space
satisfying `BorelSpace` for its inherited topology.

The definition `lowerTriangularBlockDensity T a d` is the function on `B_a`

\[
 w(b)=\operatorname{ofReal}(|\det b|_F)^{-d},
\]

where the power is the integer power in the extended nonnegative reals and
`|.|_F` is exactly `T.normalizedAbs`, with residue-cardinality normalization.
The theorem `lowerTriangularBlockDensity_eq_coe` identifies it with the
coercion of the negative integer power of the nonnegative determinant
character `T.determinantNorm`. Since that character takes values in units,
the density is finite and strictly positive. The theorem
`continuous_lowerTriangularBlockDensity` proves continuity by pulling back the
published quotient density along the actual quotient map and subgroup inclusion.

For every scalar `AdditiveHaarMeasure` `eta`, and s-finite measures `rho_a` and
`rho_d` on the two actual triangular groups, set

\[
 D=(\rho_a.withDensity\;w)\times(dx\times\rho_d),
 \qquad dx=\mathrm{rectangularMeasure}\;\eta\;d\;a.
\]

The association of the product is part of the assertion. Assume that both
triangular measures are right invariant. No positivity, regularity,
normalization, or unimodularity assumption on them is required. In particular,
the result applies to arbitrary sigma-finite right Haar measures and also allows
the zero measure.

The main theorem `measurePreserving_lowerBlockWeightedProduct_mulRight` states
that for every `g : B_a`, `y : M`, and `h : B_d`, the map

\[
 (b,X,t)\longmapsto(bg,\;Xg+ty,\;th)
\]

is measurable and preserves `D`. Matrix products use the underlying matrices of
the triangular elements. This is the parameter formula for right multiplication
of lower-block matrices; this module proves the measure assertion directly on
the parameter space and makes no homeomorphism or quotient assertion.

The implemented proof has three steps.

1. `map_lowerTriangularBlockDensity_mulRight` transports a density under the
   measurable equivalence of right translation. Right invariance of `rho_a`
   and the determinant character identity give
   `map (b -> b*g) (rho_a.withDensity w) = |det g|_F^d • rho_a.withDensity w`.
   A private change-of-density lemma is proved by equality of integrals on
   measurable sets. `map_rectangularMeasure_mulRight` specializes the published
   p-adic rectangular Haar scaling theorem to obtain the inverse scalar
   `|det g|_F^(-d)` for `X -> X*g`.
2. `measurePreserving_lowerBlockWeightedProduct_diagonal` applies the two
   pushforward identities and right invariance of `rho_d` to the product map
   `(b,X,t) -> (b*g,X*g,t*h)`. Product-measure scaling and the nonzero determinant
   cancel the two finite nonnegative scalars exactly.
3. `measurePreserving_lowerBlockWeightedProduct_shear` proves preservation by
   `(b,X,t) -> (b,X+t*y,t)`. After exchanging the matrix and last triangular
   coordinates, this is a measurable skew product over the identity, whose
   fibres are additive Haar translations. This shear theorem needs only
   s-finiteness of `rho_a,rho_d`, with no triangular invariance premise. Finally,
   compose the shear with parameter `y*g^(-1)` and the diagonal map. Matrix
   distributivity and the actual inverse identity give `X*g+t*y`.

The definition and proof are derived internal mathematics. They use the
published determinant character and quotient density, actual subgroup and
rectangular measure definitions, the published p-adic rectangular scaling proof,
and Mathlib density transport, product pushforward, additive translation and
skew-product theorems. Worker 936 proposed the diagonal/shear decomposition;
Worker 113 implemented this helper. No original-literature theorem is claimed
by this unit. The unchanged full disintegration target still requires the
actual chart geometry and the positive normalized equality of quotient measures.
