# Exact all-test formula for the actual adjoint determinant

`DynamicAdjointDeterminantFormulaStatement` is an unproved proposition target
for the constructions in `Dynamic.AdjointDeterminant`. It works over an
arbitrary commutative base ring, with actual represented dynamic `P` and `U`,
affine `P` and `U`, and natural finite coordinates on the actual Lie kernel of
`U`. These are the inputs of the conditional construction. The separate
structural and existence targets derive them from connected reductivity over
every field.

The target requires four exact comparisons:

- On every scheme test, the action recovers `p*u*p⁻¹` after the inclusions into
  the actual ambient `G`.
- On every affine test, the constructed matrix representation acts by the
  actual differential in the chosen natural Lie coordinates.
- On every affine test, the value of the constructed algebraic character is
  the intrinsic determinant of that differential on the actual Lie module.
- On every scheme test, evaluation of the character is the determinant of
  the point matrix of the constructed algebraic representation.

The representation and character are the constructions, not supplied
representations or characters. Affine tests range over every commutative
test algebra, including nonreduced algebras and field extensions. Scheme
tests are arbitrary objects over the affine base. The rank may be zero,
and there are no characteristic, splitness or root-reduction restrictions.

This target is internal packaging of the published
`AutomorphicAction.finiteRepresentation_affineAction`,
`AutomorphicAction.determinantCharacter_eval`,
`AutomorphicAction.determinantCharacter_affinePoints` and the actual
dynamic normalized-conjugation formula. It adds an exact proposition
boundary for a focused proof successor; it does not assert that the
proposition has been proved.

The motivating local-field conventions are Renard, 9 July 2026 version,
§V.3.1–V.3.4, printed p.110 (PDF p.116), and §V.5.4, printed pp.126–127
(PDF pp.132–133), and Waldspurger (2003), §I.1, journal pp.238–239
(PDF pp.4–5). The broader ring and test scope comes from the internal
construction, not a verbatim assertion in those sources. In particular,
this is the algebraic determinant with positive conjugation orientation.
No Haar measure, absolute value, square root or analytic modulus is part
of this statement.
