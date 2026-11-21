# Naturality of the adelic and idele-class norms

`Langlands.Global.AdelicFunctoriality.adeleNorm_equiv` and
`ideleClassNorm_equiv` identify the norms in a commuting square of number-field
isomorphisms. For `L/K` and `L'/K'` and compatible isomorphisms `e : K ≃+* K'`
and `f : L ≃+* L'`, applying the norm after transport along `f` agrees with
transporting the norm along `e`. The equalities are pointwise on actual adeles
and idele classes. All four fields may have independent universes.

## Proof

The field norms commute by `Algebra.norm_eq_of_equiv_equiv`. The formulas on
diagonals for the adelic norm and the arithmetic equivalences therefore give
the comparison on elements coming from `L`. To extend this comparison, the
proof uses density separately at infinity and in the product of the finite
completions, not density of the global diagonal in the full adeles.

- At infinity the two maps are continuous on the infinite adele ring, where
  the diagonal is dense.
- At a finite place of `K'` both sides are continuous functions on the
  Cartesian product of the finite completions of `L`: one reindexes and
  transports the upper coordinates before applying `finiteNormComponent`, and
  the other applies `finiteNormComponent` at the corresponding place of `K`
  before transporting that coordinate. The diagonal is dense in this product
  by `exists_algebraMap_mem_open` with no conditions at infinity, applied to a
  basic open with finitely many restricted coordinates. Equality on each
  coordinate gives equality on finite adeles.
- On an idele-class representative, both maps are induced by the maps on
  adelic units. Equality on the underlying adeles implies equality of the
  units and hence of the classes.

## Provenance

These are derived compatibility lemmas for the Library's constructed norms
and arithmetic equivalences, generalizing the private same-field
`adeleNorm_equiv` and `ideleClassNorm_equiv` arguments in
`HarrisProposition48MackeyCharacterProof.lean` (in the `Conjugation` section).
The idele-class comparison is used to identify the conjugate Mackey inducing
characters in the proof of Harris (1998), Proposition 4.8, printed pp.202–203
(registered source `harris-1998-local-langlands`, `math_9611226v1.tex`,
lines 1579–1597 and 1646–1655).
