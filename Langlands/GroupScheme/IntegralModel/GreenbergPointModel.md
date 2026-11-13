# Smooth affine residue-field models of congruence-level points

`Langlands.GroupScheme.IntegralModel.GreenbergPointModelStatement.{u}` is
the part of the Greenberg functor that the proof of Kaletha–Prasad Lemma
A.4.26 uses, stated at the level of points. It is a prerequisite for
`Langlands.GroupScheme.ConnectedGenerationStatement`. It is an unproved
proposition; this module proves nothing.

## Statement

Let `R` be a discrete valuation ring (`IsDomain`,
`IsDiscreteValuationRing`) in universe `u` whose residue field
`k = IsLocalRing.ResidueField R` is algebraically closed. Let `n : ℕ+` be a
positive level. Write `Xₙ` for
`(GroupScheme.baseChange (congruenceBaseMap R n)).obj X`, the base change of
a group scheme `X` over `Spec R` to `Spec (R ⧸ 𝔪ⁿ)`. Then `rationalPoints Xₙ`
is the group `X(R/𝔪ⁿ)` of its sections.

For every group scheme `X` over `Spec R` whose structure morphism is affine
and smooth, the proposition asserts the existence of:

- a group scheme `G` over `Spec k` whose structure morphism is affine and
  smooth;
- a group isomorphism `eX : X(R/𝔪ⁿ) ≃* G(k)`;

such that, for every group scheme `Z` over `Spec R` with affine smooth
structure morphism and every homomorphism `h : Z ⟶ X`, there exist:

- a group scheme `G_Z` over `Spec k` whose structure morphism is affine and
  smooth;
- a group isomorphism `eZ : Z(R/𝔪ⁿ) ≃* G_Z(k)`;
- a homomorphism of group schemes `g : G_Z ⟶ G`,

with `eX (hₙ z) = g (eZ z)` for all `z ∈ Z(R/𝔪ⁿ)`. Here `hₙ` is
`rationalPoints.map` of the base change of `h`, and `g` acts on points by
`rationalPoints.map g`. Moreover, if the structure morphism of `Z` is
geometrically connected, so is that of `G_Z`.

`G` and `eX` are chosen once for `X`. `G_Z`, `eZ` and `g` may depend on the
pair `(Z, h)`.

## Source and provenance

This is a derived statement. It collects consequences of the Greenberg
functor in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- **Construction and points.** The introduction to Section A.4 (printed
  pp. 603–604 / PDF pp. 634–635) introduces `Gr(X)` over the residue field
  of an artinian local ring. Its motivating property is
  `X(R) = Gr(X)(f)`. The paragraph before Theorem A.4.19 (printed p. 628 /
  PDF p. 659) defines `Grₙ(X)` as the Greenberg functor of `X ×_o (o/mⁿ)`,
  functorial in `X`. When `o/mⁿ` is an `f`-algebra it uses Weil restriction
  instead. When `char(f) = 0` this requires a non-canonical `f`-algebra
  structure on `o/mⁿ`. Definition A.4.20 (printed p. 629 / PDF p. 660) uses
  `X(o/mⁿ) = Grₙ(X)(f)`.
- **Smoothness and affineness.** Theorem A.4.19(1)–(2) (printed p. 628 /
  PDF p. 659): `Grₙ(X)` is smooth when `X` is smooth, and affine when `X` is
  affine.
- **Connectedness.** Theorem A.4.19(4): `Grₙ(X⁰) = Grₙ(X)⁰` for group
  schemes. With (3) its proof gives that `Grₙ(Z)` is connected when `Z` is
  smooth with connected fibres. The proof of Lemma A.4.26 (printed p. 632 /
  PDF p. 663) uses exactly this for the groups `Yᵢ`.

The proposition is these facts with `G = Grₙ(X)`, `G_Z = Grₙ(Z)`,
`g = Grₙ(h)`. `eX` and `eZ` are the identifications of points. The square
commutes because the point identification is natural in the scheme.

The Lean form differs from the source as follows.

- Only affine smooth group schemes are treated. The source allows smooth
  separated schemes locally of finite type.
- Only the points of the models enter. `G`, `G_Z` and `g` are asserted to
  exist, with no functor `Grₙ` and no universal property over all
  `k`-algebras. This existential form allows the non-canonical `f`-algebra
  structure the source uses when `char(f) = 0`. One choice serves `X` and
  every `Z` at once, because `eX` is fixed before `Z` and `h`.
- The source works over the book's Henselian discrete valuation ring with
  perfect residue field. The proposition assumes only a discrete valuation
  ring with algebraically closed residue field, so Henselian and complete
  rings are not required. The construction depends only on the artinian
  ring `R/𝔪ⁿ`, which is unchanged under completion. The registered
  corrections `kaletha-prasad-2024-corrections` (1 November 2024), SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF p. 49, add "perfect" before "residue" in the introduction to Section
  A.4. Algebraic closedness implies that.
- Connectedness is expressed by `GeometricallyConnected` on both sides. Over
  the algebraically closed field `k`, a connected `k`-scheme is
  geometrically connected. The hypothesis on `Z` covers all its fibres,
  including the special fibre, which is the fibre the source needs.
