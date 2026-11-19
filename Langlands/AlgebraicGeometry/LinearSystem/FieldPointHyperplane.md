# Vanishing of linear combinations at field-valued points

This internal support unit relates the vanishing of a section at a
field-valued point to hyperplane incidence under the morphism to projective
space defined by a linear system. Let `X` be a scheme over a commutative ring
`K` with structure map `p`, `L` a line bundle on `X`, and
`s 0, …, s n` global sections of `L` with no common zero (`hs`). Let
`linearSystemMap p hs : X → ℙⁿ_K` be the morphism they define (Library module
`Langlands.AlgebraicGeometry.LinearSystem.Morphism`).

## Declarations

- `linearPolynomial_mem_grading`: the polynomial `∑ i, C (c i) * X i` is
  homogeneous of degree one, that is, it lies in `projectiveSpaceGrading K n 1`.
- `vanishesAlong_linComb_iff`: let `F` be a field and `y : Spec F → X` a point.
  The section `linComb p s c = ∑ i, c i • s i` vanishes along `y`
  (`VanishesAlong L y`, meaning its pullback along `y` is zero) if and only if
  `∑ i, C (c i) * X i` lies in the homogeneous prime of the image point
  `linearSystemMap p hs (y closedPoint)`. In other words, the image point lies
  on the hyperplane with coefficients `c`.

## Proofs

The degree statement is a sum of products of a constant with a variable, each
homogeneous of degree one.

For the equivalence, choose `j` with `y(closedPoint)` in the nonvanishing open
of `s j` (`exists_mem_trivializationOpen`). Since `Spec F` has one point, `y`
lands in that open everywhere. Then:

1. `vanishesAlong_iff_sectionRatio_eq_zero` turns vanishing into the vanishing
   of the ratio `linComb / s j` along `y`;
2. `sectionRatio_linComb_eq_chartRingHom` writes this ratio as the image of
   `∑ i, C (c i) * X i` under the chart ring map `chartRingHom p s y j`;
3. `comp_linearSystemMap` identifies `y ≫ linearSystemMap p hs` with the
   chart point map `pointMap p s y j`, and `chartMap_preimage_basicOpen`
   computes the preimage of the projective basic open of the linear form as
   the basic open of its image under the chart ring map;
4. membership in the homogeneous prime is, by definition, the negation of
   membership in the projective basic open.

It remains to see that an element `r` of `Γ(Spec F, ⊤)` is zero exactly when
the closed point is outside its basic open. If `r = 0`, its basic open is
empty. Conversely, if the only point is outside the basic open, the basic open
is empty, and `eq_zero_of_basicOpen_eq_bot` on the reduced scheme `Spec F`
gives `r = 0`. The proof follows the forward argument of the Library lemma
`exists_not_mem_hyperplane_of_linComb_ne_zero` (module
`Langlands.AlgebraicGeometry.LinearSystem.Nondegeneracy`), but runs it in both
directions at a field-valued point.
