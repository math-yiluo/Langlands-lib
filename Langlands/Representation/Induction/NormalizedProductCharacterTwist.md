# Common determinant twists of actual normalized block induction

Authors: Worker 468; Worker 6 (adapted determinant and tensor argument).

This is internal algebraic support for reducing a rank-one test to the trivial
character. It generalizes the determinant/tensor argument in the published
`Classification.TwistedProductCharacterTwistProof` from segment factors to
arbitrary block representations. It uses the published
`Induction.smoothInductionTwistEquiv` directly, which works without smoothness
of the inducing representation. No new literal literature theorem is asserted.

For any p-adic field, supplied `TopologicalData T`, ordered block shape `B`,
smooth scalar character `χ` of the field's units, and actual block
representations `σ i`, the main definition
`T.normalizedProductDeterminantTwistEquiv B χ σ` is an actual equivalence
from the determinant twist of `T.normalizedProductInduced B σ` to the same
normalized construction applied to all determinant-twisted block factors.
The field and block-carrier universes are independent. The blocks retain their
original dependent carriers, order, and sizes. All block shapes and ranks are
allowed. No smoothness, admissibility, finite dimension, irreducibility, or
full Whittaker-type hypothesis on the block representations is required.

The determinant of a parabolic element is the product of the determinants of
its Levi projection blocks, by the published `determinant_blockParabolic`.
Its restriction to the Levi section gives the corresponding embedding formula.
Restrict the smooth ambient determinant character along that embedding.
Its individual coordinate characters are exactly the block determinant
characters. The published `SmoothCharacter.external_coordinate_twist` then
identifies the actual tensor actions.

`normalizedProductDeterminantTwistInducing_eq` uses these determinant
identities and commutation of complex scalar multiplication to identify the
two actual parabolic covariance actions, retaining the same positive
half-modulus. `normalizedProductDeterminantTwistInducingEquiv` bundles the
identity linear map between those actions.

The main equivalence composes the published smooth-induction character
equivalence with induction of this identity coefficient equivalence.
The generic character equivalence already proves covariance, linearity,
inverse laws and equivariance on the actual smooth induced function spaces.
Its uniform right stabilizer is obtained by intersecting the original open
stabilizer with the determinant character's open kernel. The two evaluation
lemmas here hold by definition: the map sends `f(g)` to `χ(det g) • f(g)`,
and the inverse multiplies by the inverse unit.

This construction supplies an actual representation comparison. It does not
provide analytic convergence, full Whittaker type, gamma or L certificates,
factor existence, lower-to-upper reversal, or either two-block analytic base.
It assumes a smooth character and does not assert that arbitrary continuous
characters are smooth; the separate published open-kernel theorem can supply
that input when applicable.

The determinant calculation reuses
`Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding`
from the published refinement modulus calculation.
