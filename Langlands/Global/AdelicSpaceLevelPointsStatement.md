# Adelic-level points of separated finite type algebraic spaces

Author: Worker 105.

`AdelicSpaceLevelPointsStatement` states Proposition 5.2 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.13, for global fields of both characteristics. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
only states the result and contains no proof.

Conrad's Proposition 5.2 reads: "Let `X_S` be a separated algebraic space of
finite type over `O_{F,S}`. The map (3.6.1) is bijective." The map (3.6.1) is
defined in Theorem 3.6 (printed p.6): "Using the projections from `A_{F,S}` to
`F_v` for `v ∈ S` and to `O_v` for `v ∉ S`, the natural map of sets
`X_S(A_{F,S}) → ∏_{v∈S} X_v(F_v) × ∏_{v∉S} X_{S,v}(O_v)`". Here `F` is a global
field, and `S` is a finite set of places, "non-empty and containing the
archimedean places, as always" (printed p.5).

## Finite type spaces over a ring

`FiniteTypeOverRing C X`, for an actual algebraic space
`X : AlgebraicSpace (Spec (CommRingCat.of C))` over the spectrum of a commutative
ring `C`, is `HasAtlasProperty (@LocallyOfFiniteType ⊓ @QuasiCompact) X`. It says
that there exist an actual scheme `U` over `Spec C` and a surjective étale
transformation from `U` to `X` whose structure morphism `U ⟶ Spec C` is both
locally of finite type and quasi-compact. `HasAtlasProperty` is from
`Langlands/AlgebraicGeometry/AlgebraicSpace/StructuralAtlasGeometry.lean`.

This is the Stacks Project notion of a morphism `X → Spec C` of finite type. The
registered source is `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`
(Stacks Project version ed88ff78, chapters Properties of Algebraic Spaces and
Morphisms of Algebraic Spaces; registered folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`).

- Morphisms of Spaces, Definition 23.1 (Tag 03XF): "We say `f` is of finite type if
  it is locally of finite type and quasi-compact."
- Morphisms of Spaces, Definition 8.2 (Tag 03HE): `f : X → Y` is quasi-compact if
  `Z ×_Y X` is quasi-compact for every quasi-compact algebraic space `Z` mapping to
  `Y`.
- Properties of Spaces, Definition 5.1 (Tag 03E3): "`X` is quasi-compact if there
  exists a surjective étale morphism `U → X` where `U` is a quasi-compact scheme."
- Morphisms of Spaces, Lemma 23.4 (Tag 040Y): `f` is locally of finite type if
  and only if (6) some surjective étale `U → X` from a scheme has `U → Y` locally
  of finite type, if and only if (7) this holds for every étale `U → X` from a
  scheme.

The definition agrees with this notion because the base `Spec C` is affine. Since
`Spec C` is quasi-compact, Definition 8.2 with `Z = Spec C` shows that `X → Spec C`
is quasi-compact if and only if `X` is quasi-compact. Suppose `X → Spec C` is of
finite type. Definition 5.1 gives a surjective étale `U → X` from a quasi-compact
scheme, and `U → Spec C` is locally of finite type by Lemma 23.4(7). Conversely,
an atlas as in the definition shows that `X` is quasi-compact (Definition 5.1)
and locally of finite type over `Spec C` (Lemma 23.4(6)). The definition is
stated only over affine bases.

## The statements

- `NumberFieldSpaceLevelPointsStatement`: let `K` be a number field, `S` a finite
  set of finite places, and `O = (S : Set (FinitePlace K)).integer K` Mathlib's
  ring of `S`-integers. Let `X` be an algebraic space over `Spec O` with
  `IsSeparated X` and `FiniteTypeOverRing O X`. Then the map sending
  `p : RingPoints O X (numberFieldAdeleLevel K S)` to the family
  `i ↦ RingPoints.changeRing (numberFieldLevelFactorAlgHom K S i) p` is
  bijective.
- `CurvePlaceSpaceLevelPointsStatement`: let `k` be a finite field and `F` a
  function field over `k` (Mathlib's `FunctionField k F`). Let `S` be a nonempty
  finite set of places `AlgebraicCurve.Place k F`, and `O = curvePlaceSIntegers k F S`.
  For every algebraic space `X` over `Spec O` with `IsSeparated X` and
  `FiniteTypeOverRing O X`, the map sending
  `p : RingPoints O X (curvePlaceAdeleLevel k F S)` to
  `i ↦ RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F S i) p` is
  bijective.
- `AdelicSpaceLevelPointsStatement` is the conjunction of the two, in a common
  universe.

The level rings and their factors are the published ones from
`Langlands/Global/AdelicLevelModelPoints.lean`. For a number field the index
`NumberFieldLevelFactorIndex K S` runs over all infinite places, the finite
places in `S`, and the finite places outside `S`. The factors are the
corresponding completions, completions, and completed rings of integers. For a
function field the index runs over the places in `S` and outside `S`, with the
completions and the completed valuation rings as factors. Each
`...LevelFactorAlgHom K S i` is the coordinate projection, an algebra map over
the `S`-integers. The `S`-integers act on every factor through it, so each factor
point `RingPoints O X (factor i)` is a point of `X` with values in that factor.

## Relation to the source and derived content

`RingPoints O X A` is the set of `A`-valued points of `X` over `O`, as defined in
`Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`. Conrad writes the
local factors as `X_v(F_v)` and `X_{S,v}(O_v)`, the points of the base changes of
`X_S`. For an `O`-algebra `A`, the `A`-points of a base change of `X_S` along
`O → A` are the `A`-points of `X_S` over `O`. The statement uses the latter form
directly, so no base change of algebraic spaces is needed. `IsSeparated X` (the
diagonal is a representable closed immersion) is Conrad's separatedness
hypothesis. Separated spaces are quasi-separated, which matches Conrad's
Section 5 convention.

For a number field, `S` ranges over finite sets of finite places. The archimedean
places are always factors of the level ring, as in Conrad's convention that `S`
contains them, and this makes Conrad's set nonempty. For a function field, Conrad's
nonemptiness is the hypothesis `S.Nonempty`. "Global function field" is
formalized as a function field over a finite constant field `k`, with places
`AlgebraicCurve.Place k F`.

Also derived here: the names, the packaging of the two characteristics, and the
use of `RingPoints.changeRing` along the published coordinate projections as the
map (3.6.1).

## Not stated here

The proof of Proposition 5.2 uses an affine étale atlas, a uniform bound on fibre
degrees, unramified extensions of degree `N!` of the local rings, a finite étale
cyclic cover of the product ring and étale descent. These are proof material.
The topology on `X_S(A_{F,S})` obtained from this bijection and Proposition 5.4,
discussed on printed p.17, is not stated here.
