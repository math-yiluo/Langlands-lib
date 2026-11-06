# The two fullness steps for an actual unitary geometric piece

This derived supporting construction assembles the two intersection
fullness arguments in Renard, *Représentations des groupes réductifs
p-adiques*, edition dated 9 July 2026, VII.2.6 theorem, uniqueness proof,
printed p.231 / PDF p.237. Its input is an actual
`GeometricLemmaIntersectionDatum D` for the original parabolics and a
`D.NonzeroUnitaryPieceMap ha' σ τ`. The source of that map is the published
unitary geometric piece: normalized induction along `D.q'` of the inner
unitary Jacquet module of `σ`, pulled back along the actual conjugation
equivalence `D.e`. The target is the original representation `τ`.

`NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable` assumes
normalized-exponent temperedness and square-integrability modulo the
center of `σ` for an arbitrary specified Haar measure on `M(F)/Z(M(F))`,
together with the exact published
`TemperedSquareIntegrableUnitaryPartStatement`. The existing intrinsic
nonvanishing theorem makes the inner unitary Jacquet part nonbottom.
The proof extracts the central character from the square-integrability
datum. If `D.p'` were proper, the forward direction of the supplied
criterion would make that same part bottom. This contradiction proves
`IsIso D.p'`. This step does not need irreducibility or semisimplicity.

`NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable` assumes
irreducibility, normalized-exponent temperedness and square-integrability
of `τ` for an arbitrary specified Haar measure on `L(F)/Z(L(F))`.
It also requires semisimplicity of the actual induced unitary piece,
temperedness of its literal inducing representation
`SmoothRep.pullback D.e (leviUnitaryJacquetModule ... σ)`, a split
component of the actual second intersection Levi `D.L'`, and the exact
same square-integrability criterion at the target carrier universe.
It applies `isIso_of_squareIntegrable_semisimple_induction_quotient`
with precisely this induced representation and the stored nonzero map.
That construction splits the quotient map, uses tempered reciprocity
to prove nonvanishing of the unitary Jacquet part of `τ` along `D.q'`,
and contradicts the criterion for a proper second intersection.
This establishes `IsIso D.q'`. Its inputs suffice independently of the
first fullness result.

`unitaryPieceConjugacyOfSquareIntegrableNonzeroMap` assumes both sets
of inputs and irreducibility of both original representations. It
installs the two proved isomorphism instances and applies
`unitaryFullPieceConjugacyOfNonzeroMap` to the unchanged actual nonzero
map. The resulting `FullPieceConjugacy` stores an isomorphism `M ≅ L`,
the ambient conjugacy equation by the inverse of the original rational
point, and a complex linear equivalence of the original carriers
intertwining their actions by the point map of that same scheme
isomorphism.

The field universe `u`, source carrier universe `v` and target carrier
universe `w` are independent. The two criterion inputs are instances
of the exact published proposition at `v` and `w`, respectively.
Every actual parabolic, Levi and radical datum is retained, with the
canonical ambient and Levi point topologies and their derived local
compactness and nonarchimedean group instances.

All analytic and geometric hypotheses described above remain explicit.
This file neither proves the supplied square-integrability criterion
nor constructs the geometric filtration or the nonzero piece map.
It does not establish temperedness or semisimplicity of that piece or
its inducing representation. Those remain separate obligations in
the final VII.2.6 application. No final VII.2.6 statement is proved
or modified.
