# Morphisms to projective space glued from local homogeneous coordinates

Module `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateAtlasGluing`,
namespace `Langlands.AlgebraicGeometry.CoordinateAtlas`.

Let `K` be a commutative ring, `X` a scheme with a morphism
`p : X ⟶ Spec K`, `V : ι → X.Opens` a family of opens (any index type), and
for each `i` a family `c i : Fin (m + 1) → Γ(X, V i)` of functions on `V i`.
All schemes lie in one universe `u`.

## Definitions

- `pull g hg : Γ(X, U) →+* Γ(Z, ⊤)` pulls a function on `U` back to a global
  function along a morphism `g : Z ⟶ X` whose image lies in `U`. It is
  Mathlib's `g.appLE U ⊤`.
- `IsAtlas c` has two fields.
  - `covers`: every point of `X` lies in the basic open of some `c i σ`.
  - `compat`: for all `i k` there is a unit `u` of `Γ(X, V i ⊓ V k)` with
    `c k σ = u * c i σ` on `V i ⊓ V k` for every `σ`.

  The opens `V i` themselves need not cover `X`, but `covers` forces them to.
- `coordRingHom p c g i hg` is the ring map from the homogeneous coordinate
  ring `ProjectiveCoordinateRing K m` to `Γ(Z, ⊤)`. It sends constants through
  `g ≫ p` and `X σ` to `pull g hg (c i σ)`.
- `pointMap p c g i σ hg`, for `g` landing in the basic open of `c i σ`, is the
  Library chart map `LinearSystem.chartMap` of this ring map through the chart
  `D₊(X σ)`.
- `atlasMap p hc : X ⟶ ProjectiveSpace K m` glues the point maps of the
  inclusions of the basic opens of all `c i σ`.

## Results

- `comp_pull`, `pull_res`, `basicOpen_pull`, `isUnit_pull_iff`: naturality,
  compatibility with restriction, and the basic open of a pulled-back function.
  A pulled-back function is a unit exactly when the point lands in the basic
  open of the original function.
- `coordRingHom_scale`: on an overlap, the coordinate ring map of chart `k` is
  the one of chart `i` rescaled by a unit `a`. A homogeneous element of degree
  `n` is multiplied by `a ^ n`. Consequently `isUnit_pull_iff_of_atlas`: a
  coordinate is invertible in one chart exactly when it is in the other.
- `pointMap_eq`: the point map depends neither on the chart nor on the chosen
  invertible coordinate. `comp_pointMap`: point maps are natural in the source.
  `pointMap_toSpec`: they lie over `Spec K`. `pointMap_preimage`: the preimage of
  `D₊(X τ)` is the basic open of the pulled-back `c i τ`.
- `comp_atlasMap`: along any `g` landing in the basic open of `c i σ`,
  `g ≫ atlasMap p hc = pointMap p c g i σ hg`. `atlasMap_toSpec`:
  `atlasMap p hc ≫ projectiveSpaceToSpec K m = p`.
- `exists_unit_of_comp_eq`: let `F` be a field and `t t' : Spec F ⟶ X` with
  equal images under `atlasMap`. Suppose `t` lands in `V i` and `t'` in `V k`.
  Then some unit `a` of `Γ(Spec F, ⊤)` satisfies
  `pull t' (c k σ) = a * pull t (c i σ)` for every `σ`. The charts are
  arbitrary; the point need not lie in the basic open of a coordinate fixed in
  advance.

## Proofs

The construction follows the Library construction of linear-system maps in
`LinearSystem/Morphism`, with local functions in place of ratios of global
sections. `coordRingHom_scale` uses the unit transition and the Library lemma
`eval₂_mul_of_isHomogeneous`. `pointMap_eq` changes the chart by
`chartMap_eq_of_scale` and the coordinate by `chartMap_eq`. The glued map uses
`openCoverOfIsOpenCover` and `glueMorphisms`; the overlap condition is
`pointMap_eq` after `comp_pointMap`. `comp_atlasMap` is checked locally with
`Scheme.hom_ext_of_forall`.

For `exists_unit_of_comp_eq`, the image of the closed point lies in some
coordinate open `D₊(X τ)` (Library `iSup_projectiveSpaceCoordinateOpen`). Pulling
it back by `pointMap_preimage` shows that the `τ`-coordinate of each point is
invertible, because `Spec F` has one point. Both composites are then chart maps
through `D₊(X τ)`. `awayLift_eq_of_chartMap_eq` gives equality of the quotients
by the `τ`-coordinates, and `a` is the quotient of the two `τ`-coordinates.

## Provenance

Internal. The gluing of local maps into projective space is the standard
construction of a morphism from a line bundle with generating sections; the
Library module `LinearSystem/RelativeMorphism` cites it as Stacks Project,
Section 27.14, Lemma 27.14.1, tag 01NJ. Here the line bundle is described only by its
local trivializations and transition units. The module is used to construct
the torsion bracket map of `TorsionBracketMapStatement` from local powered
minors. It asserts nothing about any particular atlas.
