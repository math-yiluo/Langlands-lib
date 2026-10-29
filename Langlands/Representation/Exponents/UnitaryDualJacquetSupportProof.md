# Prescribed unitary dual-exponent tempered opposite support

Author: Worker 532.

`Langlands.glUnitaryDualJacquetTemperedSupport` proves the published
`GLUnitaryDualJacquetTemperedSupportStatement.{uF,uV}` with independent field
and source carrier universes. For every supplied p-adic topology, positive
rank, block shape, irreducible analytically tempered source and prescribed
unitary dual exponent, it constructs an actual irreducible admissible
representation of the full product Levi in the source carrier universe.
The same prescribed character acts by scalars, the representation is an
actual opposite Jacquet class exponent, it is analytically tempered modulo
the full center for every supplied Borel Haar realization, and the source
embeds into its normalized opposite parabolic induction.

The implemented proof composes published algebraic, analytic and adjunction
results. Source temperedness supplies admissibility and hence smoothness.
Irreducibility supplies finite generation over the ambient group algebra.
`Parabolic.oppositeJacquetFiniteGeneration` then gives finite generation
of the whole actual normalized opposite Jacquet module. Its admissibility
comes from `UnitaryDualJacquetSupport.jacquet_admissible`.

The ordinary dual exponent yields a nonzero functional on the full
algebraic dual by
`UnitaryDualJacquetSupport.exists_dualEigenfunctional`. Its evaluated
transpose equation uses precisely the prescribed character, without
inversion or complex conjugation. Block scalars commute with every Levi
element, and the product Levi has cofinal compact open subgroups.
`centralDualEigenQuotient` applies to these data and produces an actual
irreducible admissible scalar quotient of the whole opposite Jacquet
module. The proof keeps its surjective intertwining map `q`.

`UnitaryDualJacquetSupport.classExponent_of_quotient` uses the top
subrepresentation and `q` to witness actual class occurrence. For each
arbitrary measurable structure, Borel-space instance and Haar measure on
the Levi modulo its full center, `glTemperedJacquetClassExponent` applies
to this same class exponent and scalar character. The supplied unitary
values discharge the right side of its equivalence, establishing the
analytic `L^(2+epsilon)` conclusion for that measure.

Finally, `UnitaryDualJacquetSupport.embedding_of_quotient` applies proved
normalized opposite adjunction to `q`, source smoothness and both
irreducibility hypotheses. It gives the required actual injective
intertwiner from the whole source. Thus the embedding uses a retained
whole-Jacquet quotient, rather than any inference from class occurrence
alone.

This is an internal assembly of the proofs documented in
[UnitaryDualJacquetSupportAdapters](UnitaryDualJacquetSupportAdapters.md),
[CentralDualEigenQuotientProof](CentralDualEigenQuotientProof.md),
[OppositeJacquetFiniteGenerationProof](../Parabolic/OppositeJacquetFiniteGenerationProof.md)
and
[TemperedJacquetClassExponentProof](TemperedJacquetClassExponentProof.md).
The source motivation and normalization of the unchanged target are
recorded in [DualJacquetStatement](DualJacquetStatement.md). The proof adds
no finite-spectrum, finite-length, tensor-factorization, coefficient
comparison or semisimplicity premise. It uses no downstream support,
weakly critical refinement, tempered exhaustion, unitarity or genericity
theorem, and makes no discrete-series claim.
