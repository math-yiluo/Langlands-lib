# Descent of the character-valuation kernel

This proof establishes exactly
`Langlands.Geometry.Building.CharacterValuationKernelDescentStatement.{u}`.
The field is an arbitrary nonarchimedean local field in universe `u`, of either
characteristic, and the group is arbitrary affine. The unramified closure,
fixed-field valuation and rational norm kernel are the actual public
constructions in the target.

For the forward inclusion, the proof uses
`comap_characterValuationKernel_le` and the equality between the canonical
character-valuation kernel and the rational common norm kernel.

For the reverse inclusion, a character over the unramified closure has the same
values on extended base-field rational points as a character over a finite
Galois intermediate field. The finite-field character's norm character is
defined over the base field. Its evaluation is the field norm of the original
value, by `normCharacter_eval`. The hypothesis puts this norm evaluation in the
canonical valuation's unit kernel.

The compatible local-field norm also gives value one on a canonical valuation
unit. Galois invariance of the spectral norm expresses the norm of the field
norm as a positive integer power of the spectral norm of the finite-field
value. This forces that spectral norm to equal one. Compatibility of spectral
norms in field towers identifies it with the prescribed fixed-field valuation
on the unramified closure, proving the required character-value condition.

This is a derived proof of the public target. The implementation uses the
finite-coefficient and corepresented character construction, the generic affine
norm-character construction, and the spectral-norm power formula already
described in their companion files. It needs no reductivity, smoothness,
connectedness, finite-type or splitting hypothesis.
