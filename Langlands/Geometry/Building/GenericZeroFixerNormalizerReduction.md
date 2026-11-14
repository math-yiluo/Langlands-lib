# Generic finite zero-fixer reduction to the normalizer

This internal support draft for Task 6309 adapts the implemented finite-set
induction in `ZeroFixerNormalizerReduction` to apartment data over any field,
with a connected reductive group and a maximal split torus. It uses the published
`ApartmentFacetClosureFixing` for generic cocharacters and the unipotent/normalizer
stabilizer step, together with the sibling draft modules
`GenericFiniteSharpExchange` and `GenericPositiveRootFixerCoordinates`.

The ambient subgroup `H` contains every sharp fixer. The subgroup `Q` of the
actual rational normalizer acts trivially on the entire apartment and maps into
`H`. The proposed finite fixer is the join of the image of `Q` and the sharp
fixer. Covariance of sharp fixers makes this join the product in either order.
The exact conditional premise `HasNormalizerSharpFixers` states that every
normalizer point in `H` fixing a finite nonempty subset lies in that join.
This premise remains explicit; it is not proved by this module.

The singleton argument uses the quotient stabilizer decomposition and this
normalizer premise. Generic finite sharp exchange decomposes an element of the
proposed join into positive-root fixers, negative-root fixers, and a normalizer
point in `H` fixing the finite subset.

For the insertion step choose one old point and a generic cocharacter adapted
to the direction to the new point. The positive factor remains in the sharp
fixer after insertion, by the root-filtration translation formula. Removing it
leaves a negative-unipotent/normalizer product fixing the new point. The
published Bruhat step shows that its normalizer factor fixes the new point as
well, so the conditional normalizer premise puts that factor in the new join.
The remaining negative factor fixes every new-set image. Generic positive-root
fixer coordinates put it in the sharp fixer of the new set. The three factors
therefore all lie in the new join. Induction gives
`subgroup_pointwiseFixer_eq_trivialNormalizer_sup_sharpFixer_of_finite`.

Finally set `Q` equal to `H.subgroupOf (normalizerPoints i)` intersected with
the kernel of `D.normalizerAffineEquiv`. Its image lies in the whole-apartment
pointwise fixer within `H`. The finite upper inclusion then holds with that
whole-apartment subgroup as constant factor; the reverse inclusion follows
directly from pointwise fixation and sharp-fixer containment. This proves
`subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_finite`, retaining
the exact normalizer premise for this choice of `Q`.

No local-field structure, extra apartment axioms, normality of `H`, assertion that
the whole-apartment fixer lies in the normalizer, bounded comparison, or proof of
the final target is claimed. The mathematical provenance is internal: the
existing Library proof of KP Lemma 7.7.4 in `ZeroFixerNormalizerReduction` with
the centralizer-zero factor replaced by an arbitrary subgroup of the kernel of
the apartment action. All supporting identifications are proved for the actual
root filtrations and quotient action.
