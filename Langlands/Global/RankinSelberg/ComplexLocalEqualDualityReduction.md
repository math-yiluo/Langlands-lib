# Dual analytic clauses of the complex equal-rank functional equation

`ComplexLocalEqualDualityReductionStatement` reduces the Library's formulation of
Jacquet 2009, Theorem 2.1 (i)–(iii) for the complex equal-rank local integrals, to two premises.
`ComplexLocalEqualPrimalAnalyticStatement` supplies absolute convergence, holomorphy and
meromorphic continuation of each original integral with its original test function.
`ComplexLocalEqualMeromorphicEquationStatement` supplies the codiscrete equality with the
Library factors for continuations that agree with the original and dual integrals on a common
right half-plane. Both premises remain open.

The proof first applies the primal premise to the given data. Inverse transpose with the long
Weyl element transports the two Whittaker functions to the models for the reversed inverse
lists, with the additive parameters negated. The exact trace Fourier transform of the given
test function is Schwartz. These transported data give another instance of the original
integral, which is definitionally the dual integral after substituting the Fourier transform.
Applying the primal premise to this instance proves the dual analytic clauses. Taking the
larger of the two convergence thresholds gives a common right half-plane on which both
continuations agree with their integrals. The equation premise then gives the exact
codiscrete identity.

This is an internal reduction using `ComplexLocalDualWhittaker`, `ComplexLocalFourierSchwartz`
and the published local equal-rank statement. It applies at every rank index.
