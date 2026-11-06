# Conjugacy from an actual full unitary geometric piece

This derived supporting construction supplies the unitary-piece endpoint
of the uniqueness argument in Renard, *Représentations des groupes
réductifs p-adiques*, edition dated 9 July 2026, VII.2.6 theorem,
uniqueness proof, printed p.231 / PDF p.237.

The source obtains a nonzero map from a piece
`i^L_{Q'} e^* (r^M_{P'} σ)_0` to the second inducing representation,
then proves that both intersection parabolics are full. The preceding
`ActualGeometricFullPiece` construction consumes a nonzero map from the
full geometric piece. This file connects the actual unitary piece
`D.unitaryPieceRep ha' σ` to that construction.

Both `D.p'` and `D.q'` are assumed to be isomorphisms throughout.
The actual intersection datum, normalized functors, split component
`ha'`, canonical Levi topologies and original rational-point maps are
retained. No intersection fullness or geometric filtration is proved here.

`D.unitaryFullPieceEmbedding ha' σ` constructs an injective intertwiner
from the actual unitary piece to `σ` transported along the inverse of
`D.fullLeviPointsEquiv`. Its map first evaluates the full-parabolic
induced function at the identity, includes the resulting vector of the
actual unitary Jacquet module in the full Jacquet module, and applies the
full Jacquet equivalence. The equivariance proof uses the three actual
intertwining laws in that order. Each endpoint equivalence is bijective,
and the middle map is the literal submodule inclusion, so the composite
is injective.

`D.unitaryFullPieceConjugacyOfNonzeroMap` additionally assumes that
`σ` and `τ` are irreducible and that an actual intertwiner from the
unitary piece to `τ` is nonzero. An explicit order isomorphism of
subrepresentation lattices proves irreducibility of the transported
`σ`. The embedding cannot vanish: its injectivity would make the source
zero, contradicting the given nonzero map. The nonzero-map alternative
for an irreducible target therefore makes the embedding surjective.
Its inverse extends the original map to the full geometric piece.
Nonzeroness follows by restricting this extended map back through the
two equivalences. The preceding full-piece construction then yields the
scheme isomorphism `M ≅ L`, the ambient conjugacy equation with `z⁻¹`,
and an equivalence `σ ≃ₗ[ℂ] τ` with the original-point intertwining law.

The field universe and both representation-carrier universes are
independent. The assumptions include the nonarchimedean local-field and
topological hypotheses required by the published unitary-piece
definition, along with the two explicit fullness hypotheses.
Temperedness, square-integrability, central characters and admissibility
are not assumed for this endpoint. No assertion that every full
Jacquet module is entirely unitary is used. The geometric-lemma
filtration, nonzero-piece extraction, both fullness arguments and the
three final VII.2.6 propositions remain separate obligations.
