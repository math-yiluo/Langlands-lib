# Integral lifts through split-unipotent special-fibre quotients

This internal construction combines the published Henselian reduction theorem
with the published section theorem for an affine quotient by a smooth closed
split-unipotent subgroup. Its provenance is this direct composition of Library
results. It assumes a supplied smooth integral model and a supplied represented
quotient; it asserts no model or quotient existence.

Let `R` be a Henselian local domain with fraction field `K`, in an arbitrary
universe. Let `M` be a smooth affine integral model of a `K`-group scheme.
Suppose `q : M.specialFibre → Q` is a represented fppf quotient by a supplied
smooth closed split-unipotent subgroup `n : N → M.specialFibre`, and `Q` is
affine over the actual residue field of `R`.

`IntegralModel.quotientReduction_surjective` proves that every rational point
of `Q` is the quotient image of the reduction of an integral section of `M`.
The proof first uses
`HomogeneousQuotient.fppf_section_of_split_unipotent_torsors`, discharged by
`splitUnipotentAffineTorsorStatement`, to obtain an
actual scheme section of `q`. Composing the given rational point with that
section produces a rational point of the special fibre. Then
`IntegralModel.reduction_surjective` lifts this point to an integral section.
Associativity and the section identity give its prescribed quotient image.
Rational surjectivity of an arbitrary schematic image is never assumed.

`quotientReductionLift` chooses such an integral section.
`quotientReductionLift_spec` verifies its exact image. No connectedness,
solvability or reductivity of the generic group or of `Q` is required, and
there is no characteristic restriction.
