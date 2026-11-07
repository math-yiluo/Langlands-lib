# Compact-fixed matrices for actual rational unramified induction

The construction `RationalNormalized.inducedSpecializedBasis` specializes the
published `Compact.CoefficientSpecialization.specializedBasis` to the actual
full normalized rational universal induced model. The field and representation
carrier have independent universes, as does the basis index. The ambient
rational points use their existing rational point topology. Local compactness,
the nonarchimedean group structure, the actual semidirect decomposition and
closedness of the unipotent subgroup are explicit inputs.

Fix a compact open subgroup `K`. A basis `e` over the actual regular function
algebra of the universal induced `K`-fixed module is supplied. At each character,
bijectivity of actual full-induced specialization is also supplied.
`inducedGenericScalarExtension_eq` identifies that specialization with the
generic coefficient scalar-extension map. Transporting the scalar-extended
basis through its canonical compact-fixed equivalence gives a complex basis
of the actual fiber's `K`-fixed space, with the same index.

For finite index and a supplied left Haar measure,
`inducedSpecializedBasis_fixedMatrix` applies the published coefficient matrix
formula. The entry at `g,i,j` is the evaluation at the character of the `i`-th
coefficient coordinate of the actual universal Hecke projection of
`ρ(g)(e(j))`. Both universal and specialized projections are the existing
normalized compact-fixed Hecke projections, and the fiber action is the
existing `complexInduced` action.

`inducedSpecializedBasis_continuous` assumes the actual specialization
bijection at every unramified character. For each `g,i,j` the formula identifies
the matrix-entry function with one fixed element of the evaluation-generated
regular algebra. The published `continuous_unramifiedRegularFunction` then
proves continuity for the full complex unramified character topology. This
does not restrict the parameters to the unitary characters.

These are internal derived constructions and identities from the published
actual rational specialization comparison, coefficient fixed-basis matrix
formula and regular-function continuity. Existence of the supplied coefficient
basis and specialization bijections is not asserted here.

The actual model here uses positive full-parabolic normalization. Comparison
with positive Levi normalization, uniform detection of irreducible subquotients,
and existence of an irreducible fiber remain separate obligations.
