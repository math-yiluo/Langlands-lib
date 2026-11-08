# Rational points separate characters of a split base change

Let `G` be a group scheme over a field `k` and `L / k` a field extension. This module proves
that a character of the base change `G_L` is determined by its values on the rational points
of `G`, extended to `L`. It needs one of two sets of hypotheses:

- the rational points of `G` are dense and `G_L` is reduced; or
- `k` is infinite, `L / k` is finite Galois, and `G_L` is a split torus.

The intended use is a torus `T` over `k` split by a finite Galois extension. There two
characters of `T_L` agreeing on `T(k)` are equal. The unitary root groups of a quasi-split
group need this. There the products of two embeddings of a root field, evaluated on root
values `β(z)` for `z ∈ T(k)`, are values of characters `τβ + ρβ` of `T_L`. This separation
then reduces the `hsep` hypothesis of `Langlands.Algebra.NormEquivariantBilinear` to an
identity of characters. This module makes none of these identifications.

Provenance: internal. The statement is the standard fact that a morphism out of a reduced
scheme to a separated scheme is determined on a dense set of points. The proof only combines
existing Library and Mathlib results.

## Setting

All declarations live in namespace `Langlands.GroupScheme.RationalCharacterSeparation`.
Apart from the first lemma, the variables are fields `k L : Type u` with `[Algebra k L]` and
`G : GroupScheme (Spec (CommRingCat.of k))`. The Library notions used are:

- `GaloisPointComparison.baseChanged k L G`, the base change `G_L`;
- `rationalPoints G`, the rational points of `G`, and
  `GaloisPointComparison.rationalExtend k L G : rationalPoints G →* rationalPoints G_L`,
  their extension to `L`;
- `rationalCharacters G_L`, the characters `G_L ⟶ 𝔾_m` (written additively), and
  `rationalCharacterEval ψ : rationalPoints G_L →* Lˣ`, the value of a character on a rational
  point;
- `HasDenseRationalPoints k G.X`: the rational points of `G` are dense in `G`.

## Declarations

- `ext_of_dense_iUnion_range`: a scheme lemma. Let `X` be reduced, `f g : X ⟶ Y`, and
  `s : Y ⟶ Z` separated with `f ≫ s = g ≫ s`. Let `p a : W a ⟶ X` be a family of morphisms
  whose images have dense union, with `p a ≫ f = p a ≫ g` for every `a`. Then `f = g`.
  Proof. Every `p a` factors through the equalizer of `f` and `g`. So the equalizer's image
  contains the dense union, and the equalizer inclusion is dominant. Mathlib's
  `ext_of_isDominant_of_isSeparated` then gives `f = g`.
- `SeparatesBaseChangeCharacters k L G : Prop` (definition): for all characters `ψ ψ'` of
  `G_L`, if `rationalCharacterEval ψ (rationalExtend k L G z)` equals
  `rationalCharacterEval ψ' (rationalExtend k L G z)` for every `z : rationalPoints G`, then
  `ψ = ψ'`.
- `rationalExtend_eq_geometricRationalPointHom`: `rationalExtend k L G z` is the Library's
  canonical pullback section `geometricRationalPointHom G z`. Both maps have the same first
  pullback projection (`rationalExtend_fst`, `baseChangeSectionHom_fst`). Both lie over the
  base, which fixes the second projection.
- `dense_iUnion_range_rationalExtend hG`: if `G` has dense rational points, then the images
  of the extended points `rationalExtend k L G z` have dense union in `G_L`. This is the
  Library's `dense_geometricRationalPointHom` combined with the previous lemma.
- `rationalCharacters_ext`: assume `[IsReduced G_L.X.left]` and `hG`. Two characters of `G_L`
  agreeing on every extended rational point are equal. Proof. Agreement of values is equality
  of the composite points (`Gm.affinePointsEquiv` is injective). Apply
  `ext_of_dense_iUnion_range` to the underlying scheme maps of the two characters, with `s`
  the structure map of `𝔾_m` over `L`, and the extended points as the family. Then
  `Grp.hom_ext` and `Over.OverMorphism.ext` turn the equality of scheme maps into an
  equality of characters.
- `rationalCharacters_ext_of_isSplitTorus`: assume `[Infinite k]`, `[FiniteDimensional k L]`,
  `[IsGalois k L]`, and `hT : IsSplitTorus G_L`. Two characters of `G_L` agreeing on every
  extended rational point are equal. Proof. `hT.isIntegral` makes `G_L` reduced. The Library's
  `TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange` gives dense rational
  points. Then apply `rationalCharacters_ext`.
- `separatesBaseChangeCharacters` and `separatesBaseChangeCharacters_of_isSplitTorus`: the
  two previous theorems, stated as `SeparatesBaseChangeCharacters k L G`.

## Limitations

The module compares characters only through their values on extended rational points. It does
not relate these values to embeddings of root fields or to the Galois action on characters,
and it proves no case of `hsep`.
