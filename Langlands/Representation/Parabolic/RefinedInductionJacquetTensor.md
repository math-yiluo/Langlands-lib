# Normalized induction after Jacquet on a product Levi

`RefinedInductionJacquetTensorStatement` concerns a standard block Levi over an
actual p-adic field with a supplied topological realization, and a refinement
of its block shape. If a complex representation of the coarse Levi is
equivalent to an external tensor of smooth block representations, its normalized
refined Jacquet module induced back to the coarse Levi is equivalent to the
external tensor of the normalized induction–Jacquet composites in the individual
blocks. The field and input carrier universes are independent.

`RefinedJacquetTensor.normalizedRefinedJacquetCongr` descends the input
equivalence to the normalized refined Jacquet modules.
`RefinedJacquetTensor.jacquetEquiv` identifies the quotient of the tensor with
the tensor of the block quotients on the actual refined Levi.
`RefinedInductionJacquetTensor.jacquetFactors` bundles those block quotients
as smooth representations. `normalizedRefinedInducedCongr` transports the
coefficient equivalence through normalized refined induction, and
`refinedInductionTensor` identifies the induced action with the external
tensor of the normalized induced block actions.

This comparison assembles the external-product compatibilities of compact
induction and Jacquet restriction from Bernstein and Zelevinsky's *Induced
representations of reductive p-adic groups I* (1977), Proposition 1.9(g).
Proposition 1.9(e) and §2.3 identify the compact and smooth inductions in
the parabolic setting.
