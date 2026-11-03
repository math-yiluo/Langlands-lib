# Square integrability on a compact full central quotient

`Langlands.compactCentralQuotientSquareIntegrability` proves the complete
`CompactCentralQuotientSquareIntegrabilityStatement` with independent group and
carrier universes.

Choose the genuine unitary central character supplied by the hypothesis.
Admissibility supplies smoothness of every vector. The published
`UnitaryCentralCharacter.continuous_coefficientNorm` then makes every
descended coefficient norm continuous on the actual full central quotient.
In a compact space every function has compact topological support, by
`HasCompactSupport.of_compactSpace`. Mathlib's
`Continuous.memLp_of_hasCompactSupport` gives `MemLp` at exponent two for the
supplied Haar measure, which is finite on compact sets. Together with the
original admissibility this is precisely `IsSquareIntegrableModCenter`.

No representation-theoretic input beyond the displayed admissibility and
genuine unitary central character is used. No irreducibility, finite length,
classification, Jacquet module, adjointness, character independence or
cuspidal-support result enters. Compactness of the full central quotient is
an explicit premise; this proof does not establish it for a particular group.
