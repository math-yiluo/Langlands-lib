# Cuspidal trace class of smooth test functions (statement)

`Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement` contains one
proposition definition and no proof:
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement.{u}`.

## Statement

The parameters are those of `GroupSchemeFullAEL2CuspidalTraceClassStatement`: a number field `F`, an
affine group scheme `G` of finite type over `F`, `hPD : ParabolicDynamicStatement`,
`hG : IsConnectedReductive G`, a central split torus `T → G` with the stated conditions, right
invariance of Haar measure on the norm-one subgroup, and `μG = Measure.haar` on `G(𝔸_F)`.

If every `f : C_c(G(𝔸_F), ℂ)` that is a test function (`IsAdelicTestFunction F G f`: continuous,
smooth infinite slices, compactly supported, right and left invariant under open subgroups of
`G(𝔸_f)`) has a Hilbert–Schmidt cuspidal operator
`fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf`, then every test function has a
trace-class cuspidal operator.

## Relation to the existing statement

`GroupSchemeFullAEL2CuspidalTraceClassStatement` assumes the Hilbert–Schmidt property for **every**
compactly supported continuous weight and concludes trace class for convolution products `f₁ ⋆ f₂`.
Getz–Hahn prove the Hilbert–Schmidt property for smooth weights (their Theorem 9.1.2, as quoted on
the page of the existing statement). Here the hypothesis is weakened to test functions and the
conclusion reaches every test function. It does not follow from the existing statement, whose
hypothesis is stronger; it is proved in the same way, in
`Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassReduction`, from
`Langlands.Analysis.IntegratedActionConvolutionStatement`.
