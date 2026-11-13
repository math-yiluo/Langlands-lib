# Integral points of the standard general linear integral model

This is a helper module for the proof of
`Langlands.GroupScheme.GeneralLinearLatticeIntegralModelStatement` (module
`Langlands.GroupScheme.IntegralModel.GeneralLinearLatticeProof`). It computes the
integral points of the Library's standard model
`GeneralLinear.standardIntegralModel R K (Fin N)` from
`Langlands.GroupScheme.IntegralModel.GeneralLinearLattice`. That module
implements the model but proves nothing about its integral points.

Provenance: internal. These are the elementary facts that the integral points
of the standard model `GL_{N,R}` are `GL_N(R)`, read inside `GL_N(K)`. They
are needed for the `GL(L)` paragraph of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Proposition 8.3.1 (PDF p. 327, printed p. 296). The
source uses them without proof.

Throughout, `R` is an integral domain with a supplied fraction field `K`
(`IsFractionRing R K`). No discrete valuation hypothesis is used here.

## Declarations

### `GeneralLinear.baseChangeIso_hom_entry`

Let `b : Spec R' ⟶ Spec R` be any morphism. Let `x` be a point over a test
scheme `T` of the base change of `GL_{n,R}` along `b`. Compose `x` with the
Library's identification `GeneralLinear.baseChangeIso n b` with `GL_{n,R'}`.
The pullback of the `(i, j)` coordinate function `entrySection n R' i j` along
the result equals the pullback of `entrySection n R i j` along
`x.left ≫ pullback.fst _ b`. That composite is the projection of `x` to
`GL_{n,R}`.

The proof rewrites both sides with `GeneralLinear.pointsEquiv_apply_apply`,
which turns a coordinate into a matrix entry. It then applies the Library
theorem `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom`: on points the
base-change isomorphism keeps the matrix. What remains holds by definition
(`rfl`). The Library proves the same fact in
`IntegralModel/IntegralDiagonalRepresentation.lean` (`baseChangeIso_entry`)
only for `𝒪[F] → F`. This version is for an arbitrary base morphism. The
module raises `maxHeartbeats` to 400000 for this lemma, as that Library
lemma does.

### `GeneralLinear.standardIntegralModel_integralPointMap`

For every integral section `x` of `GL_{N,R}` over `Spec R`,

`rationalPointsEquiv N (CommRingCat.of K) ((standardIntegralModel R K (Fin N)).integralPointMap x)
  = Matrix.GeneralLinearGroup.map (algebraMap R K) (rationalPointsEquiv N (CommRingCat.of R) x)`.

So the generic matrix of the integral point is the integral matrix of `x`
with each entry mapped to `K`.

The proof compares entries `(i, j)`. `GeneralLinear.rationalPointsEquiv_apply_apply`
writes both entries through `Scheme.ΓSpecIso`. By definition,
`integralPointMap x` is `baseChangeSectionHom (Spec.algebraMap R K) _ x`
composed with the model's `genericIso`, which is `baseChangeIso`. Then:

- `baseChangeIso_hom_entry` moves the coordinate to `GL_{N,R}`;
- `baseChangeSectionHom_fst` (from `Langlands.GroupScheme.IntegralModel`)
  rewrites the projection as `Spec.algebraMap R K ≫ x.left`;
- `Scheme.Hom.comp_appTop` splits the pullback;
- Mathlib's `Scheme.ΓSpecIso_naturality` for
  `CommRingCat.ofHom (algebraMap R K)` identifies pullback along
  `Spec.algebraMap R K` with `algebraMap R K`.

### `GeneralLinear.mem_standardIntegralModel_integralPoints_iff`

A rational point `g` of `GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)`
lies in `(standardIntegralModel R K (Fin N)).integralPoints` exactly when
`rationalPointsEquiv N (CommRingCat.of K) g` lies in the range of
`Matrix.GeneralLinearGroup.map (algebraMap R K)`. That is, its matrix comes
from `GL_N(R)`. The proof module's `GeneralLinear.mem_range_map_iff_exists_map`
shows that this range condition holds exactly when the matrix and its inverse
both have all entries in `R`.

Proof of the forward direction: it is the previous lemma. Backward: take
`C ∈ GL_N(R)` mapping to the matrix of `g`. Then the integral section
`(rationalPointsEquiv N (CommRingCat.of R)).symm C` maps to `g`. This follows
from the previous lemma and injectivity of `rationalPointsEquiv` over `K`.
