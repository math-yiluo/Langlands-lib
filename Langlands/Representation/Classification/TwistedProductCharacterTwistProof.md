# Common determinant-character twists of normalized block products

Author: Worker 6.

`Langlands.Classification.twistedProductCharacterTwist` proves the exact published
`Langlands.Classification.TwistedProductCharacterTwistClause.{uF,uV} F T`.
The field and block-carrier universes remain independent, and the induced carrier
lies in `max uF uV`. For every positive rank, ordered block shape, smooth scalar
character, smooth block family and real block exponents, it constructs the
actual representation equivalence between twisting the normalized product and
the normalized product of the twisted blocks. The exponents remain unchanged.

The determinant of an upper block triangular matrix is computed after
reindexing by the block-coordinate equivalence. Mathlib's block-triangular
determinant formula gives one determinant for each fiber of the block index.
Reindexing each fiber by its actual block coordinates identifies these with the
determinants of the Library's Levi projection. Restriction to the Levi section
then computes the determinant of the block embedding.

The smooth Levi character is the ambient determinant character restricted along
the continuous Levi embedding. Its coordinate restrictions are the individual
block determinant characters. The published
`Induction.SmoothCharacter.external_coordinate_twist` supplies equality of the
actual finite tensor actions, with no dimension or representation-theoretic
hypotheses.

The proof imports the published theorem `Langlands.Induction.inductionTwist`
from `Langlands.Representation.Induction.CharacterTwistProof`. This supplies the
generic induction-function equivalence without any additional theorem premise.

For a family of block representations, first apply the prescribed real powers,
take the finite external tensor, pull back along the Levi projection, and twist
by the positive half-modulus. This parabolic representation is smooth: the
tensor is smooth, the Levi projection is continuous, and the half-modulus has
open kernel. Apply the smooth-induction half of `Induction.inductionTwist` to
this representation and the ambient smooth determinant character. Its constructed
equivalence acts on the actual induced function spaces and has the prescribed
pointwise formula `f(g) ↦ χ(det g) • f(g)`. The imported construction proves
covariance, complex linearity, inverse laws and equivariance under right
translation. It preserves uniform smoothness by intersecting each function's
open right stabilizer with the character's open kernel; the inverse multiplies
by `χ(det g)⁻¹`.

The determinant twist commutes with each pre-existing real twist by commutation
of complex scalar multiplication on the unchanged block carrier. The tensor
identity above, the two determinant formulas, and scalar commutation with the
half-modulus identify the resulting parabolic coefficient action with that of
the desired normalized product. Finally,
`Induction.smoothInducedEquiv` transports the identity coefficient equivalence
`equivOfRepresentationEq` across induction, and composition gives the
equivalence in the target clause. No irreducibility, unitarity, admissibility,
finite dimension, or finite length is assumed.

The source convention was read in Bernstein and Zelevinsky (1977), §1.8,
printed p.444 / PDF p.5: positive-half covariance and a uniform open right
stabilizer, with right translation. Proposition 1.9(f), printed p.445 / PDF p.6,
states character compatibility; §2.2, printed p.446 / PDF p.7, fixes ordered upper
GL blocks. The determinant and finite tensor specialization here is a derived
algebraic argument, not a separate assertion attributed to that source.
Registered source: `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original hash was verified on 2026-10-25; neither the workspace nor the
consulted published Library contained a `notes/errata` directory.
