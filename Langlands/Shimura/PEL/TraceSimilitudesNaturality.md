# Coefficient naturality of the actual Harris trace similitudes

Worker 57. This internal derived unit makes coefficient extension explicit for
the already constructed original-involution Harris trace-form comparison.

The trace pairing commutes with every homomorphism f of commutative rational
coefficient algebras. Tensor induction in both arguments reduces this assertion
to the published pure-tensor formula, multiplication preservation and the
rational-algebra condition on f. This applies in particular to the auxiliary
inverse-unit form used for the original Harris group.

`harrisBilinearSimilitudes` abbreviates the existing left-regular-linear bilinear
similitude subgroup for that form. `harrisTraceSimilitudesMap` constructs its
coefficient homomorphism by recovering the unit from a linear automorphism's
value at one, applying the actual tensor coefficient map, and returning to the
bilinear group. Its action on every vector x in the target tensor algebra is

```text
x -> x * changeCoefficients(f)(e(1)),
```

and its multiplier is the image under f of the original unit multiplier. The
proved action identity says that applying the new automorphism to the
coefficient image of any source vector gives the image of its original action.
Thus this transport is the actual extension of the regular-module linear map.
The algebraic-to-bilinear equivalence is natural for these maps. Identity and
composition laws hold as equalities of group homomorphisms.

`harrisRationalTraceSimilitudesEquiv` constructs the analogous comparison on A
over Q. Twisting the involution by beta and then by beta inverse recovers the
original involution, so the published rational trace-form adjoint theorem and
nondegeneracy construct this comparison. No positivity hypothesis is needed.
`harrisBilinearDiagonal` then extends the rational bilinear group through the
actual tensor inclusion. Its action is right multiplication by 1 tensor e(1),
and its multiplier is the rational scalar image. All coefficient maps preserve
this diagonal.

The finite-local specialization uses the Library's actual rational finite
adeles, finite place, finite completion and finiteEvaluation algebra map.
Its compatibility with the original algebraic comparison and the rational
diagonal are proved specializations of the general identities.

All provenance is internal: this unit derives the results from the published
trace pairing, tensor extension, opposite-group comparison, recovered-unit
inverse, involution-twist cancellation and actual adelic coefficient maps.
It adds no source theorem as an assumption. No topology on the bilinear group,
continuity assertion, lattice existence, Hodge positivity or moduli
representability is asserted here.
