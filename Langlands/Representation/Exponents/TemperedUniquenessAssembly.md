# Conditional uniqueness from common embeddings and an actual unitary filtration

This is derived infrastructure for the uniqueness assertion of Renard
VII.2.6. It composes the constructions in
`TemperedInductionEmbeddingPieceMap` and
`ActualUnitaryPieceInducingTempered`; it translates no additional source
statement. In particular, it does not prove or modify
`TemperedIrreducibleDiscreteSeriesUniquenessStatement`.

`conjugacyOfInductionEmbeddingsAndUnitaryFiltration` takes an irreducible
smooth representation `π` with injective intertwiners into the normalized
inductions of irreducible representations `σ` of `M(F)` and `τ` of `L(F)`.
Both actual parabolic triples and their decomposition data are supplied.
The two original Levi representations are assumed tempered and
square-integrable modulo their respective centers for arbitrary specified
Haar measures with Borel measurable structures. The exact
`TemperedSquareIntegrableUnitaryPartStatement` is supplied at the two
original carrier universes.

The first induced representation is assumed tempered and semisimple.
A split component of `L`, a finite family of actual intersection data
`D i` at representatives `z i`, and split components of both intersection
Levis are also supplied. The input `s` is a genuine `ObjectRepFiltration`
of the actual unitary Jacquet module of the first induction along the
second parabolic. Its graded representations must be equivalent to the
literal `unitaryPieceRep` values in the supplied permutation `e`.
Every such literal unitary piece is assumed semisimple.

The implementation first extends the second embedding across the first
using semisimplicity, applies the actual tempered induction reciprocity,
and extracts a nonzero map from one of the supplied graded pieces. These
steps are the existing
`nonzeroUnitaryPieceMapOfInductionEmbeddings` construction. Applying
`unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness`
to that index derives both intersection fullness assertions and recovers
the original Levi conjugacy. First fullness supplies the temperedness of
the literal inner inducing representation, so no separate inner
temperedness hypothesis or nonzero piece map is an input here.

The result is an index `i` and the existing `FullPieceConjugacy`:
an actual scheme isomorphism `φ : M ≅ L`, the equation
`φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso (z i)⁻¹).hom`, and a complex
linear equivalence between the original carriers that intertwines
`σ(m)` with `τ(φ(F)(m))`. Thus it retains the actual rational-point action
and ambient conjugation direction.

The field, the common representation carrier, and the two original Levi
representation carriers have four independent universes. The canonical
ambient and Levi point topologies and the displayed local-field,
local-compactness and nonarchimedean hypotheses are retained.
No standardness, root presentation or chosen double-coset enumeration is
needed for this conditional composition. The actual filtration,
split-component data, original and induced temperedness, both
semisimplicity inputs and both exact square-integrability criteria remain
obligations for the unconditional uniqueness theorem. The construction
establishes none of these inputs.
