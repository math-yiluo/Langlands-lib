# The forward map from variable adjunction to relative series

Worker 56 constructed this derived unit from the published weighted evaluation,
relative scalar structures, and closed-relation descent interfaces.

## Objects and hypotheses

Let `K` be an ultrametric normed field, let `A` be a
`PresentedAffinoidAlgebra K`, and write `n = A.arity`, `r = A.polyradius`
and `I = A.ideal`. Thus `A` is the actual quotient
`K{r⁻¹T}/I` with its quotient norm. For an arbitrary positive real
polyradius `s` on `Fin m`, set

\[
 B=K\{r^{-1}T,s^{-1}Y\}/\overline{\langle i(I)\rangle},
 \qquad C=A\{s^{-1}Y\},
\]

where `i = GeneralizedTateAlgebra.appendLeft r s K`.
Here `B` is exactly `Adjoin.algebra K A s ∅`, and `C` is exactly
`GeneralizedTateAlgebra s A`, with its weighted coefficient norm and the
common-base `K`-algebra structure from `RelativeAlgebra`.

The tuple and its estimates need no completeness. Construction of the maps
assumes `CompleteSpace K`: the existing completeness instances then make `A`
and `C` complete, as required by weighted evaluation. Neither ideal properness,
`NormOneClass A`, a nontrivial valuation, nor a value-group condition on radii
is imposed. Both arities may be zero, and zero quotients are allowed.

## The explicit unit and monomial estimates

`PresentedAffinoidAlgebra.norm_one_le` proves `‖(1 : A)‖ ≤ 1` by applying
contraction of the presentation map to the scalar Tate algebra's unit.
The isometric coefficient inclusion transfers this bound to `C`.

The helper `GeneralizedTateAlgebra.monomialValue_norm_le_weight` works for
any variable type, positive polyradius `r`, normed commutative ring `D`, and
tuple `b`. Given `‖(1 : D)‖ ≤ 1` and `‖b i‖ ≤ r i`, it proves

\[
 \left\|\prod_i b_i^{d_i}\right\|\leq\prod_i r_i^{d_i}.
\]

For nonempty exponent support, the proof bounds the norm of the finite product,
uses the norm-power inequality only at the positive exponents in that support,
and multiplies the coordinate estimates. For empty support, the assertion
reduces to the explicit unit bound. Thus the proof does not need a unit norm
of exactly one, and remains valid for a zero ring.

## Evaluation in relative series

The remaining declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin`.
`relativeSeriesTuple` sends an old coordinate to the constant series with
coefficient `coordinate K A i`, and a new coordinate to `X s A j`.
Its `castAdd` and `natAdd` formulas specify the two blocks explicitly.

`norm_relativeSeriesTuple_le` bounds each entry by its appended radius.
The old block uses the isometric constant inclusion and the quotient-coordinate
bound. The new block uses the exact formula `‖X s A j‖ = ‖(1 : A)‖ * s j`
and the unit upper bound. The preceding monomial lemma gives
`relativeSeriesTuple_monomial_bound` with constant one.

`relativeSeriesEvaluation` is the published `evaluateHom` at this actual tuple,
from the enlarged scalar Tate algebra to `C`.
`norm_relativeSeriesEvaluation_le` applies its supplied-constant estimate at
one, proving contraction. `relativeSeriesEvaluation_X` gives every coordinate
value.

`relativeSeriesEvaluation_comp_appendLeft` proves an equality of bounded
`K`-algebra maps:

\[
 E\circ i=c\circ q_A,
\]

where `E` is the evaluation map, `c = constantAlgHom s K A`, and `q_A` is the
presentation map. Weighted `hom_ext` reduces the equality to old coordinates;
the variable inclusion and evaluation formulas prove each coordinate equality.
`relativeSeriesEvaluation_appendLeft` is the resulting pointwise identity.
It implies `relativeSeriesEvaluation_relations`: every included element of `I`
vanishes under `E`, and there are no additional equations.

## The descended map and its laws

`relativeSeriesMap` applies `descendRelations` to `E` and this vanishing proof,
constructing an actual bounded `K`-algebra homomorphism

\[
 \Phi:B\longrightarrow C.
\]

Continuity and the published closed-relation descent ensure that the entire
closed generated ideal is annihilated. The defining representative formula is
`relativeSeriesMap_presentationMap`, namely `Φ(q_B(f)) = E(f)`.

`norm_relativeSeriesMap_le` transfers the constant-one evaluation bound through
the quotient norm:

\[
 \|\Phi(b)\|\leq\|b\|.
\]

`relativeSeriesMap_baseMap` proves `Φ(baseMap(a)) = c(a)` by choosing a
representative of `a` and applying the base-map, descended-map and old-block
formulas. `relativeSeriesMap_newCoordinate` proves `Φ(newCoordinate(j)) = X s A j`
by the representative formula and the second-block evaluation identity.

## Provenance and scope

The source context is Vladimir Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), Definition 2.1.6(i), printed/PDF page 8. The registered
source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
That definition describes the relative weighted restricted series and their
coefficient norm. The existing `GeneralizedTateAlgebra s A` realizes those series:
for finitely many variables, cofinite weighted decay agrees with decay as total
degree tends to infinity. The actual quotient `B` and its base map come from
the previously published `Adjoin` construction.

The present forward comparison, its contraction bound and its map laws are
derived here from those concrete objects, weighted evaluation and quotient
descent. They are not attributed to a numbered comparison theorem in the source.
The auxiliary norm estimates have the broader hypotheses explicitly stated above.

This unit proves no injectivity, surjectivity, exact kernel description,
isometry of `Φ`, or independence from the presentation of `A`. Those are further
comparison obligations. It also supplies no analytic atlas, analytic-domain
representation or etale site.
