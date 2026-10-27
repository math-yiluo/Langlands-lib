# Scalar Jacquet integrability on the actual cell submodule

`Langlands.Whittaker.TwoBlockCellJacquetIntegrabilityStatement` states that the
ordinary scalar Jacquet integrand of every vector of the actual
`twoBlockCellSubmodule` is integrable. It allows every linear functional from
the inducing tensor carrier to the complex numbers and every measure on the
rectangular matrix space that is finite on compact sets. In particular it
applies to additive Haar measure. The topology and Borel structure come from
the canonical p-adic topological data.

There is no topology on the tensor carrier and no continuity assumption on the
linear functional. Smooth induced functions are locally constant. Composing
with any scalar linear functional preserves local constancy, hence gives a
continuous scalar function after restriction to the continuous cell
representatives `w n(x)`. The cell submodule's defining compact support
condition then bounds the support of this scalar restriction. Multiplication
by the continuous Jacquet kernel preserves compact support and continuity.

This is a derived internal prerequisite, using the definitions of
`twoBlockCellSubmodule` and `jacquetIntegrand` and the published local constancy
law `Langlands.Induction.eval_isLocallyConstant`. The support-in-the-cell part
of submodule membership is not needed for this assertion; compact support of
the restriction suffices. It asserts no right-translation stability, global
Jacquet convergence, or Whittaker extension theorem.
