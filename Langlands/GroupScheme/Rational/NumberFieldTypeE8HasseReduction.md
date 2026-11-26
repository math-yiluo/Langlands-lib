# The Hasse kernel in type E₈: totally complex fields and the real places

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE8HasseReduction`.

The module states two theorems on simply connected absolutely almost-simple groups of
type `E₈` over number fields. It proves that together they give the published
statement `NumberFieldTypeE8HasseStatement` (module
`Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction`). The two
statements are not proved in this module.

## The common hypotheses

Both statements use the hypotheses of `NumberFieldTypeE8HasseStatement`. They
quantify over a field `K : Type u` (written `F` in the second statement) with
`[NumberField K]` and a group scheme `G` over `Spec K` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`. They also quantify over actual Tits index data
`d : TitsIndexData G` and a bijection `e : d.Vertex ≃ Fin 8` with
`d.cartan a b = CartanMatrix.E 8 (e a) (e b)` for all simple vertices `a, b`. They
assume `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. Cocycles live on the
finite Galois field covers `GaloisCocycle.cover K L`, i.e. on `Spec L → Spec K`.

## `NumberFieldTotallyComplexTypeE8Statement`

Add the hypothesis `[NumberField.IsTotallyComplex K]`: every infinite place of `K` is
complex. The conclusion has two parts:

- `IsQuasiSplit G`: `G` is connected reductive and has a Borel subgroup defined over
  `K`;
- for every field `L : Type u` that is a finite Galois extension of `K`, every cocycle
  `ξ : Cocycle G (GaloisCocycle.cover K L)` satisfies `ξ.IsTrivial`.

This is the case `K` totally imaginary of the assertion in Platonov–Rapinchuk,
§6.8, printed p. 386 (PDF p. 395), paragraph "Groups of type E₈": `H¹(K, G) = 1` over
a local or totally imaginary number field `K`, and every group of type `E₈` over such
a field splits. The source proves it with Theorem 6.29 (printed p. 378), whose case
`p = 5` for `E₈` rests on Chernousov's Theorem 6.30 (printed p. 387) and Propositions
6.23–6.25 (printed pp. 389–394). The Lean conclusion records quasi-splitness, which
follows from splitness. (Conversely a quasi-split group of type `E₈` is split, since the
`E₈` diagram has no nontrivial automorphism; this comparison is not formalized here.)

## `NumberFieldTypeE8QuadraticSplittingHasseStatement`

Let `F` be a number field with `G`, `d` and `e` as above. Let `L : Type u` be a field
with `[Algebra F L]`, `[Algebra.IsQuadraticExtension F L]` (so `[L : F] = 2`) and
`[NumberField.IsTotallyComplex L]`. Write `G_L` for the base change
`(GroupScheme.baseChange (algebraBaseMap F L)).obj G`. Assume:

- `IsQuasiSplit G_L`;
- for every field `M : Type u` that is a finite Galois extension of `L`, every cocycle
  `ζ : Cocycle G_L (GaloisCocycle.cover L M)` is trivial.

The conclusion is that of `NumberFieldTypeE8HasseStatement`. For every field
`M : Type u` that is a finite Galois extension of `F`, every cocycle
`ξ : Cocycle G (GaloisCocycle.cover F M)` with `ξ.LocallyTrivial` satisfies
`ξ.IsTrivial`. Local triviality is triviality after pullback to the full cover at
every place of `F`, archimedean places included.

This is the step from the totally imaginary case to an arbitrary number field in
Platonov–Rapinchuk, printed p. 386: "The Hasse principle can then be derived exactly
as in the case of E₇". The paragraph "Groups of type E₇" on the same page uses a
totally imaginary quadratic extension `L/K` over which `G` splits. Lemma 6.17 (printed
p. 330, PDF p. 339) gives a Borel `L`-subgroup `B` with `T = B ∩ σ(B)` a maximal
`K`-torus, where `σ` generates `Gal(L/K)`. The class becomes trivial over `L`, so it is
a class of `Gal(L/K)`. Lemma 6.28 (printed p. 369, PDF p. 378) replaces it by an
equivalent cocycle in the kernel of `H¹(K, T) → ∏_{v real} H¹(K_v, T)`. The source
gives the remaining step only for `E₇`. The hypotheses of the Lean statement are what
this argument uses about `L`.

## The reduction

`numberFieldTypeE8Hasse_of_totallyComplex_of_quadraticSplitting` proves

```
NumberFieldTotallyComplexTypeE8Statement.{u} →
  NumberFieldTypeE8QuadraticSplittingHasseStatement.{u} →
    NumberFieldTypeE8HasseStatement.{u}
```

Fix `F`, `G`, `d`, `e`, a finite Galois cover `M/F` and a locally trivial cocycle `ξ`.

- If `F` is totally complex, the second part of the first statement over `F` makes
  `ξ` trivial.
- Otherwise `exists_totallyComplex_quadratic_intermediateField` gives an intermediate
  field `E` of `SeparableClosure F` with `Algebra.IsQuadraticExtension F E` and
  `NumberField.IsTotallyComplex E`. `E` is finite over `F` and hence a number field
  (`NumberField.of_module_finite`). `SeparableClosure F` is a separable closure of `E`,
  and `IsSepClosure.equiv` gives an `E`-algebra isomorphism
  `c : SeparableClosure E ≃ₐ[E] SeparableClosure F`. The published
  `TitsIndexData.separableScalarExtension` (module
  `Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension`) supplies actual
  Tits index data for `G_E` together with a bijection of simple vertices that preserves
  every Cartan entry. Composing its inverse with `e` gives an `E₈` numbering for
  `G_E`. `isSimplyConnected_fieldExtension_iff` and
  `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension` carry simple
  connectedness and absolute almost-simplicity to `G_E`. The first statement over `E`
  then gives quasi-splitness of `G_E` and the triviality of its finite-Galois cocycles.
  These are the hypotheses of the second statement for `L = E`, which makes `ξ`
  trivial.

Two private instances give `IsAffineHom` and `LocallyOfFiniteType` for the structure
morphism of a base change `G_E`, which is a pullback of the one of `G`.

## Auxiliary results

- `isTotallyComplex_of_isSquare_neg_one`: a field in which `-1` is a square is totally
  complex. A real infinite place would give a ring map to `ℝ` sending a square root of
  `-1` to a real number whose square is `-1`.
- `exists_totallyComplex_quadratic_intermediateField`: a number field that is not
  totally complex has, inside its separable closure, a quadratic extension that is
  totally complex. Take `i` with `i ^ 2 = -1` in `SeparableClosure F`
  (`IsSepClosed.exists_pow_nat_eq`) and `E = F(i)`. By the first auxiliary result,
  `-1` is not a square in `F`. So `X ^ 2 + 1` has no root in `F` and is irreducible,
  hence equal to the minimal polynomial of `i`, and
  `IntermediateField.adjoin.finrank` gives `[E : F] = 2`. Since `-1 = i * i` in `E`,
  `E` is totally complex.

## Sources

- V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press,
  1994 (`platonov-rapinchuk-1994-algebraic-groups-number-theory`). §6.8: the
  paragraphs "Groups of type E₇" and "Groups of type E₈", printed p. 386 (PDF p. 395).
  Lemma 6.17 is on printed p. 330, Lemma 6.28 on printed p. 369, Theorem 6.29 on
  printed p. 378 and Theorem 6.30 on printed p. 387.
