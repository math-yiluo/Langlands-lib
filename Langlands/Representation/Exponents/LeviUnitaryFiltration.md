# Supplied filtrations on the actual unitary Levi Jacquet module

This internal construction implements the ambient-model passage used when
taking the unitary portions of a supplied geometric-lemma filtration in Renard
2026, VII.2.5 (printed p.230 / PDF p.236). It uses the characteristic spaces of
VII.1.1 and the zero/nonzero real-part partition of VII.2.3.

`leviUnitaryJacquetFiltration` takes an actual finite filtration of the Levi
Jacquet module, intersects it with the sum of generalized weight spaces whose
normalized real part vanishes, and transports that filtration along
`selectedLeviJacquetEquivUnitary`. Its ambient object is exactly the published
`leviUnitaryJacquetModule`, with its actual Levi-point action. The construction
needs no admissibility assumption. It retains the same finite length and order,
including repeated steps and zero grades. The membership theorem says that a
unitary vector lies in a transported step precisely when its underlying ambient
vector lies in the corresponding original step.

`leviUnitaryJacquetFiltrationGradedEquiv` identifies each actual successive
quotient of this transported filtration with the selected part of the
corresponding original quotient. It first reverses the equivalence on quotients
induced by transport, then uses `selectedGradedEquivOfAdmissible`. Admissibility
of the ambient Levi Jacquet representation is an explicit premise: it supplies
weight spanning of each embedded upper step. This is a supplied-filtration
comparison and does not prove that this ambient representation is admissible,
construct a geometric filtration, identify the selected geometric pieces, or
prove `TemperedGeometricLemmaStatement`.

`exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom` applies this
construction to an arbitrary supplied `IsGluedFrom` witness for the published
`leviJacquetInductionFunctor`. Evaluating that witness at a representation of
the inducing Levi gives an object filtration and the original permutation.
The preceding graded comparison, followed by `selectedWeightEquiv` on each
evaluated graded isomorphism, identifies its transported grades with the
zero-real-part selected parts of the supplied pieces. The conclusion has
exactly the actual unitary Jacquet ambient object used in VII.2.5. Both the
gluing witness and admissibility of its Jacquet-induction value remain explicit
premises. No temperedness premise by itself is asserted to imply either one,
and identifying selected pieces with `unitaryPieceRep` remains separate work.
