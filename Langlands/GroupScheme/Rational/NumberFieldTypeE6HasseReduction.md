# The type `E_6` Hasse kernel from totally complex fields and quadratic covers

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE6HasseReduction`.

The module states two cases of the Hasse principle for simply connected absolutely
almost-simple groups of type `E_6` over number fields and proves that together they give the
published `NumberFieldTypeE6HasseStatement` (module
`Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction`). The two statements are
not proved in this module.

## The common hypotheses

Both statements quantify over a number field `F : Type u`, an affine, locally finite-type
group scheme `G` over `Spec F`, actual Tits index data `d : TitsIndexData G` and a bijection
`e : d.Vertex ≃ Fin 6` carrying the actual Cartan pairings `d.cartan` to
`CartanMatrix.E 6`. They assume `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. These
are exactly the hypotheses of `NumberFieldTypeE6HasseStatement`; as there, nothing is
assumed about the star action, so inner forms (`¹E_6`) and outer forms (`²E_6`) are both
covered. Mathlib's `CartanMatrix.E 6` numbers the vertices as Bourbaki does, shifted by one:
the vertex `i` is Bourbaki's `α_{i+1}`.

## The statements

- `NumberFieldTotallyComplexTypeE6VanishingStatement`: if moreover
  `NumberField.IsTotallyComplex F` (no real place), then for every finite Galois extension
  `L/F` in universe `u`, every cocycle `ξ : Cocycle G (GaloisCocycle.cover F L)` is trivial.
  No local hypothesis is made. This is the vanishing `H¹(K, G) = 1` for `K` a totally
  imaginary number field, stated on finite Galois covers.
- `NumberFieldTypeE6QuadraticHasseStatement`: for every field `E : Type u` that is a number
  field, a finite Galois extension of `F` of degree `Module.finrank F E = 2`, and totally
  complex, every cocycle `ξ : Cocycle G (GaloisCocycle.cover F E)` with `ξ.LocallyTrivial` is
  trivial. Local triviality is triviality after pullback to the full cover
  `Spec (F_v ⊗_F E) → Spec F_v` at every place `v` of `F`, archimedean places included. This
  is the localization kernel of `H¹(E/F, G)` for a totally complex quadratic extension `E/F`.

## Sources

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory` (printed page `p` is the one-based
PDF page `p + 10`), prove Theorem 6.6 (printed p. 286) for groups of type `E_6` in §6.8 in
two steps, following Harder (1966):

- On printed pp. 382–383 ("Groups of type `¹E_6`") they show `H¹(K, G) = 1` for every simply
  connected group of type `¹E_6` over a local field or a totally imaginary number field `K`,
  and on printed p. 385 ("Groups of type `²E_6`") the same for type `²E_6`. Over a totally
  imaginary number field this is the first statement. The argument uses Proposition 6.21,
  Theorem 6.29, Proposition 6.22 and Lemmas 6.31 and 6.32 (printed pp. 375–382) and the
  isotropy Theorem 6.26 (printed pp. 352–356).
- On printed pp. 383–385 they prove the Hasse principle for `¹E_6` over an arbitrary number
  field `K`, and on printed p. 385 they indicate the same argument for `²E_6`. A class in the
  kernel of localization becomes trivial over `L = K(√-1)` by the first step, so it lies in
  `H¹(L/K, G)`; Lemmas 6.17', 6.28' and 6.33 then show it is trivial. The second statement is
  this argument for a totally complex quadratic extension `E/F`; the book's proof uses only
  that `L/K` is quadratic and `L` totally imaginary.

Both statements also follow from Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`. Theorem 25.64(a) (printed p. 562) says that for a semisimple
simply connected group over a global field the localization map on `H¹` has trivial kernel.
The second statement is the restriction of that kernel to classes split by the quadratic
extension `E/F`; it is the case `L = E` of `NumberFieldTypeE6HasseStatement`. The first
statement has no local hypothesis, so it needs one more step: over a totally complex number
field every place is nonarchimedean or complex. At a nonarchimedean place, `H¹` of a simply
connected group vanishes by Theorem 25.61(a) (printed p. 561); at a complex place the
completion is algebraically closed, so `H¹` vanishes there too. Every class is therefore
in the localization kernel, and Theorem 25.64(a) makes it trivial.

## The reduction theorem

`numberFieldTypeE6Hasse_of_totallyComplex_quadratic` assumes the two statements and proves
`NumberFieldTypeE6HasseStatement.{u}`. Take `F`, `G`, `d`, `e`, a finite Galois extension
`L/F` and a locally trivial cocycle `ξ` on `GaloisCocycle.cover F L`.

- If `F` is totally complex, the first statement applies to `ξ` directly.
- Otherwise `F` has a real place, so `-1` is not a square in `F`
  (`TypeE6HasseReduction.sq_ne_neg_one_of_isReal`: a real embedding would send a square root
  of `-1` to a real number with square `-1`). Choose `i` in the separable closure of `F` with
  `i ^ 2 = -1` (it is algebraically closed, since `F` has characteristic zero) and let `E` be
  the intermediate field `F⟮i⟯` (`TypeE6HasseReduction.gaussField`). The polynomial `X^2 + 1`
  is monic, of degree two and has no root in `F`, hence it is irreducible and is the minimal
  polynomial of `i`; so `Module.finrank F E = 2`
  (`TypeE6HasseReduction.finrank_gaussField`). A quadratic separable extension is Galois
  (`TypeE6HasseReduction.isGalois_gaussField`), and `E` is totally complex because it
  contains a square root of `-1` (`TypeE6HasseReduction.isTotallyComplex_gaussField`).
- The base change `G_E` satisfies the hypotheses of the first statement over `E`. It is
  affine and locally of finite type over `Spec E` because these properties are stable under
  base change. It is simply connected by `isSimplyConnectedFieldExtension` and absolutely
  almost-simple by `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`. Since `E` is
  an intermediate field of the separable closure of `F`, the separable closure of `F` is also
  one of `E` (`TypeE6HasseReduction.closureEquiv`), and
  `TitsIndexData.separableScalarExtension` gives actual Tits index data of `G_E` with a
  bijection of simple vertices preserving every Cartan entry. Composing it with `e` numbers
  the vertices of `G_E` by `CartanMatrix.E 6`.
- `TypeE6HasseReduction.exists_common_galois` embeds `L` and `E` into the finite Galois
  extension of `F` generated in the separable closure by their images. Call it `M`; it is a
  finite Galois extension of `E`. The first statement over `E` makes the restricted
  cocycle `GaloisCocycle.scalarExtension ξ` on the cover `M/E` trivial, and
  `GaloisCocycle.isTrivial_baseChange_of_scalarExtension` gives triviality of the base change
  of `ξ` to `E` on the full pullback cover.
- `Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel` (module
  `Langlands.GroupScheme.Rational.NumberFieldHasseInflation`), with the second statement for
  `E/F` as its kernel hypothesis, makes `ξ` trivial.

The original group, cover and cocycle are those of the target statement; no hypothesis is
added.
