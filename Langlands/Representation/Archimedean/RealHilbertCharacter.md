# Conjugation-invariant character distributions of real Hilbert actions

Let a jointly continuous real general linear group action on a complex
Hilbert space have a real-linear family of bounded integrated operators.
Each operator is given by the Bochner formula with a real smooth test
evaluated on the underlying real matrix and a Borel measure finite on
compact sets. Assume that each integrated operator is trace class.

Every matrix coefficient of this integrated family is continuous in the
test function. The proof pushes the measure forward to the matrix space.
The ordinary Hilbert matrix coefficient, extended by zero off the units,
is integrable on each compact set inside the open units because its
preimage in the group is compact. Its distribution therefore has precisely
the required coefficient by change of measure and bounded linearity of
the inner product. The trace continuity theorem gives a character in
Mathlib's space of complex-valued distributions on the open units.

For a measure invariant under both left and right multiplication,
pulling a test back by conjugation changes the integrated operator by
inverse conjugation. Cyclicity of the trace gives conjugation invariance
of the character. This internal construction uses the Library's
trace-class continuity and trace cyclicity results.
