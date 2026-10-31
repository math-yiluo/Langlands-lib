# Central-character transport on actual automorphic determinant twists

Author: Worker 2. This internal construction applies the actual central-character
transformation under determinant multiplication to the existing automorphic
and operator-realization carriers over every number field `F : Type u`.
Coefficients are complex. The character `χ` is finite order; the specified
central character `ω` is any continuous Hecke character.

`CentralCharacterAutomorphicForms.finiteOrderDeterminantMultiplier` is an
actual continuous complex-linear equivalence from the existing automorphic
space of central character `ω` to that of central character `χ^n * ω`,
for every natural rank including zero. The proof combines actual automorphic
preservation with the published ambient central-character transformation.
The inverse character gives reverse membership, since
`(χ⁻¹)^n * (χ^n * ω) = ω`; actual inverse multiplication proves the required
source-to-target submodule image equality. The equivalence is the restriction
of the original automorphic multiplier, with inherited subtype topology.
Its forward and inverse evaluation and finite right-covariance formulas are
actual determinant multiplication and inverse multiplication, with the
positive character factor in right covariance.

`OperatorRealization.determinantTwist_hasCentralCharacter` transports the
specified central-character condition on an actual full realization to its
actual total image twist. Every image vector has an original preimage under
the constructed multiplication equivalence. Applying the actual ambient
transformation to that preimage proves the condition for each vector.
The resulting central character is exactly `χ^n * ω`.
The corresponding `determinantTwist_hasCentralCharacter_iff` also reflects
this condition: apply inverse determinant multiplication to each image vector,
cancel the character powers, and use the actual inverse multiplication law
to recover the original function.

With the explicit compactness instance needed by the actual normalized
constant terms, the same submodule image argument also preserves cuspidality
in both character directions. This constructs
`CentralCharacterCuspidalForms.finiteOrderDeterminantMultiplier` between the
existing specified-character cuspidal automorphic spaces and proves its
forward/inverse evaluation and finite covariance formulas.
`CuspidalOperatorRealization.determinantTwist_hasCentralCharacter` specializes
the full realization result to the existing positive-rank cuspidal objects,
using the actual rank `r + 1` in the character power.
The corresponding cuspidal theorem also gives the equivalence of the original
and transformed central-character conditions.

The provenance is direct internal restriction and image construction using
`CentralCharacterDeterminantMultiplier`, `AutomorphicDeterminantMultiplier`,
`OperatorDeterminantTwist`, and the existing character and cusp conditions.
No new original-literature comparison is asserted. This does not claim
central-character invariance for arbitrary equivalences of embedded
realizations, existence of a prescribed-character nonzero realization,
or weak-association compatibility.
