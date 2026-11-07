# Selected-weight restriction for a scalar-character target

This internal derived construction restricts intertwiners to selected
central weight spaces when the target has one supplied scalar character.
It uses the published generalized-weight spaces and selected parts and
introduces no new source or representation-theoretic existence assertion.

The coefficient field `R`, the acting group `A`, the represented locally
profinite group `M`, and the source and target carrier universes are
independent. A homomorphism `ι : A → M` has central image. The target action
is assumed to be multiplication by a supplied character `ψ` on that image.
Neither smoothness nor admissibility of the target is assumed. The theorem
with source admissibility additionally requires that `R` be algebraically
closed; the earlier vanishing and supplied-span theorems do not.

`generalizedWeightSpace_eq_bot_of_scalar_ne` proves that a generalized
weight for a character `χ ≠ ψ` is zero in the target. A hypothetical nonzero
weight vector is annihilated by a uniform power of each scalar difference
`ψ(a) - χ(a)`. Over a field, the nonzero vector forces each difference to
vanish, contradicting inequality of the characters. The proof extracts the
power from the actual compact-open generalized-weight membership; it makes
no claim about nonsmooth vectors outside those spaces.

For a character predicate `P` with `P ψ`, any intertwiner from the source
kills the entire sum of weights with `¬ P χ`. The published weight
preservation theorem maps each generating weight into the target's same
weight, which is zero by the preceding result. Taking the submodule
supremum proves `intertwiner_eq_zero_on_excludedWeights`.

`scalarTargetWeightRestriction` is the actual complex- or field-linear
precomposition with the subtype inclusion of `selectedWeightPart`. Its
construction assumes no scalar action, spanning or admissibility. Under
the scalar action and a supplied spanning equality for the selected and
excluded parts, two maps with equal restrictions have difference zero on
both generating parts. Their difference has kernel equal to the whole
source, proving injectivity.

For an admissible source over an algebraically closed field, the existing
`CentralDecomposition.admissible_centerFinite` and
`generalizedWeightSpace_iSup_eq_top` supply spanning. The existing selection
partition identity then removes the explicit spanning premise.
`hom_rank_le_selectedWeightPart_of_scalar` applies injective-linear-map
cardinal rank monotonicity. The source and target carriers need not have
equal universes, and no finite-dimensionality is assumed.

For the intended square-integrable Jacquet application, one can take `P` to
select unitary split-component characters. A unitary central character of
the inducing representation then supplies `P ψ` directly, so the target's
full normalized-exponent temperedness is unnecessary for this restriction
argument. This module does not construct that actual split-component
specialization, prove Jacquet admissibility or its regular conjugate
filtration, or prove generic irreducibility.
