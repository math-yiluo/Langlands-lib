# Whole-operator rationality for tensor products

This internal algebraic helper extends the published
`UnramifiedOperatorFamilies`, `CompactIntertwiningComposition` and
`RationalUnramifiedOperatorContinuation` interfaces. Its purpose is the
tensor construction in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, V.3, formula (1), printed p.295 / PDF p.61, using the
whole-operator denominator convention of IV.1, printed pp.276–277 /
PDF pp.42–43 (registered source `waldspurger-2003-plancherel`).

The parameter group and scalar algebra are the existing actual
`unramifiedCharacters ν` and `unramifiedRegularFunctions ν`. The abstract
norm-character family `ν` is visible; specialization to all rational norm
characters is a separate application. The module neither replaces the actual
standard integral family nor asserts its analytic continuation.

`IsPolynomialOn.bilinear` expands the first vector family in finitely many
fixed vectors. Applying the fixed bilinear map to each fixed vector gives a
linear map on the second family. The existing regular-scalar and finite-sum
laws complete the proof. `IsPolynomialOperatorOn.tensor` uses this result on
pure tensors, then tensor induction and addition for all input tensors.
The source and target vector spaces have independent universes and need
no finite-dimensionality hypothesis.

`IsRationalOperatorOn.tensor` chooses the product of the two existing
denominators before testing any input tensor. The polynomial numerator is
the tensor of the two cleared operators. Thus the result keeps a single
denominator for the entire tensor operator.

`RationalOperatorContinuationData.tensor` constructs that particular
presentation from the two displayed global polynomial numerators, even when
their original starting regions differ. Its starting region is their
intersection, and its regular region is exactly the intersection of their
displayed regular regions. The continued operator is the tensor of the
two displayed continued operators there, by scalar bilinearity and inversion
of the product denominator.

For the normalized coefficient comparison this helper is applied only after
the second tensor factor has been identified with the inverse of the
particular reverse dual operator. This module supplies no rationality of
that inverse, no scalar-composition theorem, no nonempty or dense generic
locus, and no extension at zeros of an individual denominator. In particular
the displayed intersection is a presentation domain, not the all-unitary
regularity conclusion of V.3.1.
