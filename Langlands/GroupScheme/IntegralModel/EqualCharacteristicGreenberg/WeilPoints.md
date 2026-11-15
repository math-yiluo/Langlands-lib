# Rational points of affine Weil restriction

This module identifies the rational points of the published affine Weil
restriction `AffineWeil.groupScheme A B G` with the rational points of `G`. It
also proves that the identification is natural in `G`. The universe `u` is
arbitrary. Rational points are the published `rationalPoints G`, the sections
`Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X` of a group scheme over
`Spec A`, with the pointwise group law. All declarations lie in the namespace
`Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg`.

## Rational points as points with coefficients in the base ring

Let `A` be a commutative ring in `Type u` and let `G` be a group scheme over
`Spec A`.

- `ringCoeffEquiv A G` is a multiplicative equivalence from `rationalPoints G`
  to `G.affinePoints (CommAlgCat.of (CommRingCat.of A) A)`. These are the points
  with coefficients in `A` viewed as an `A`-algebra. The equivalence is the
  group-valued functor of points `G.points` applied to the published
  over-scheme isomorphism `ringTestSelfIso A`. That isomorphism identifies the
  spectrum of `A` as an `A`-algebra with the identity test object.
- `ringCoeffEquiv_left` states that this equivalence does not change the
  underlying scheme morphism: `(ringCoeffEquiv A G x).left = x.left`.
- `ringCoeffEquiv_map` states naturality. For a homomorphism `f : G ⟶ H` of
  group schemes over `Spec A`, applying `ringCoeffEquiv A H` after
  `rationalPoints.map f` agrees with applying `G.affinePointsTarget f` at the
  coefficient algebra `A` after `ringCoeffEquiv A G`.

## Weil restriction

Let `A → B` be a homomorphism of commutative rings in `Type u` with
`Module.Finite A B` and `Module.Projective A B`. Let `G` and `H` be group
schemes over `Spec B` whose underlying schemes are affine and locally of finite
type over `Spec B`. These are the hypotheses of the published
`AffineWeil.groupScheme`.

- `basePointsEquiv_map` states that the published base-point comparison
  `AffineWeil.basePointsEquiv` respects restricted homomorphisms. For
  `f : G ⟶ H`, applying `AffineWeil.basePointsEquiv A B H` after the action of
  `AffineWeil.map A B f` on `A`-coefficient points agrees with applying
  `G.affinePointsTarget f` at the coefficient algebra `B` after
  `AffineWeil.basePointsEquiv A B G`. The proof unfolds the comparison into
  `AffineWeil.pointsEquiv` followed by `AffineWeil.tensorUnitPointsEquiv`. It
  rewrites with the published `AffineWeil.map_affinePoints`. It concludes by the
  naturality of `G.affinePointsTarget f` along the tensor-unit isomorphism
  `B ⊗[A] A ≅ B`.
- `weilRationalPointsEquiv A B G` is a multiplicative equivalence from
  `rationalPoints (AffineWeil.groupScheme A B G)` to `rationalPoints G`. It is
  the composite of `ringCoeffEquiv` over `A`, then
  `AffineWeil.basePointsEquiv A B G`, then the inverse of `ringCoeffEquiv` over
  `B`.
- `weilRationalPointsEquiv_map` states naturality. For `f : G ⟶ H`, the
  comparison of `H` applied to `rationalPoints.map (AffineWeil.map A B f) x`
  equals `rationalPoints.map f` applied to the comparison of `G` at `x`. The
  proof applies the injective map `ringCoeffEquiv B H` and combines the two
  naturality lemmas above.

The module only reorganises existing comparisons. It makes no new
construction on schemes and does not change the restriction. In the
equal-characteristic Greenberg proof, `A` is the residue field and `B` is a
congruence quotient. The ring map is a coefficient field from the sibling
module `CoefficientField`, and `G` is the base change of the given model.
This explains the finite-projective hypotheses: a finite module over a field is
free. That use is made in `EqualCharacteristicGreenbergProof`, not here.

## Provenance

This is internal infrastructure. It makes concrete the defining property of Weil
restriction, `R_{B/A}(X)(A) = X(B)`. Kaletha–Prasad use it for
`Gr_n(X) = R_{(o/m^n)/f}(X ×_o (o/m^n))` in the paragraph before Theorem A.4.19
of *Bruhat–Tits Theory: A New Approach* (2023), printed p.628 / PDF p.659. The
book is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. No
literature theorem beyond the published `AffineWeil` comparisons is used.
