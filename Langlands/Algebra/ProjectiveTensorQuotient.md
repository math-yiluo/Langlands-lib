# Quotients representing projective tensor vanishing

This derived algebra unit extends `ProjectiveTensorCoefficients`. It constructs
`vanishingQuotient I`, the quotient of A by the coefficient ideal of a set I in
A tensor P. For arbitrary R-algebras A and B and projective R-module P,
`existsUnique_lift_iff` proves that a map A to B factors uniquely through this
quotient exactly when all tensors in I become zero in B tensor P. The quotient
itself satisfies these equations (`vanishingQuotient_kills`). There are no
finite-generation or flatness hypotheses.

The proof uses the coefficient ideal's kernel criterion and Mathlib's universal
property of an algebra quotient. For a commutative R-algebra C,
`algebraTensorMap_apply` identifies the usual algebra tensor map with the
linear tensor map in the coefficient construction. `coefficientIdeal_mono`
records monotonicity in the set of equations.
`coefficientIdeal_le_ker_iff_ideal` packages the criterion for an ideal I of
A tensor C, asserting that the tensor algebra map kills I. `coefficientIdeal_map` proves
that extending I along an arbitrary coefficient-algebra map commutes with
forming its coefficient ideal. Its forward inclusion tests against the
quotient by the extended coefficient ideal; its reverse inclusion uses
monotonicity and compatibility for images of sets.

This supplies an internal affine algebra step toward the closed fixed-locus
construction in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), Proposition A.8.10(1), printed pp. 547–549. It does not yet construct a
scheme or assert gluing, descent, or closed representability.
