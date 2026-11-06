# Central-character data and the zero case for tempered representations

Author: Worker 17.

This internal supporting construction supplies the actual
`Langlands.UnitaryCentralCharacter` datum required by the published
square-integrability predicate. It assumes exactly normalized-exponent
temperedness and a prescribed scalar central character. It does not assume
that the representation is nonzero or that the prescribed character is
unitary.

## Construction

`IsNormalizedExponentTempered.unitaryCentralCharacter` splits on whether the
carrier is nontrivial. In the nontrivial case it retains the prescribed
character. The published `SmoothRep.HasCentralCharacter.isOpen_ker` derives
its open kernel from smooth scalar action and a nonzero vector, and
`normalizedTemperedCentralCharacter` supplies norm one on the full abstract
center. The scalar action is the original hypothesis. The theorem
`unitaryCentralCharacter_character` records that this branch uses the
prescribed character.

On a subsingleton carrier every scalar acts identically on the only vector.
The construction chooses the trivial character, whose kernel is the whole
center and whose values have norm one. A prescribed scalar character on a
zero representation need not itself be unitary, so this branch makes no such
claim.

## Zero representation

`IsNormalizedExponentTempered.isSquareIntegrableModCenter_of_subsingleton`
proves square-integrability for every measurable Borel structure and Haar
measure on the actual quotient by the full abstract center. Admissibility is
extracted from temperedness. For the constructed datum, every descended
absolute coefficient is identically zero: the vector is zero, and quotient
induction reduces evaluation to the coefficient on a group representative.
`MeasureTheory.MemLp.zero` proves the required integrability.

`unitaryJacquetPart_eq_bot_of_subsingleton` needs no temperedness or central
character. The actual coinvariant quotient map is surjective, so its target
is subsingleton when the original carrier is subsingleton. The normalized
Jacquet module has that same carrier. Consequently every vector in its
unitary part is zero, proving that the part is bottom for every actual
parabolic, without a properness restriction.

## Scope and provenance

The construction composes the published full-center unitarity theorem,
scalar-character regularity, normalized Jacquet quotient and coefficient
definitions. The elementary zero-carrier argument also occurs privately for
analytic temperedness in
`Langlands.Representation.Classification.TemperedExponentEdgeProof`; the
present declarations apply to the represented-parabolic normalized-exponent
predicate, square-integrability and its actual unitary Jacquet parts.

Field and carrier universes remain independent. The local-field hypotheses,
canonical point topology, ambient local compactness and nonarchimedean group
are retained. No finite-length, irreducibility, presentation, structural
compactness or extra admissibility hypothesis is added.

This supplies the central-character input and both sides of the zero-carrier
case needed by `TemperedSquareIntegrableUnitaryPartStatement`. It proves
neither that whole statement nor `UnitaryJacquetPartTemperedStatement`.
The nonzero square-integrability equivalence still requires Casselman's
criterion and nested-parabolic face and exponent comparisons.
