# The finite and compact representations of actual determinant twists

Author: Worker 2. This internal comparison uses the actual full operator
realizations over each number field `F : Type u`, every natural rank including
zero, and complex coefficients. The Hecke character `χ` has finite order
when constructing its actual image realization.

`HeckeCharacter.finiteAdelicDeterminant` and `compactAdelicDeterminant` are
the continuous pullbacks of the actual determinant character along the finite
adelic inclusion and the standard infinite compact inclusion. These character
definitions themselves permit arbitrary continuous Hecke characters.

`OperatorRealization.determinantTwistFiniteEquiv` identifies the finite action
on the constructed actual image with the existing `Langlands.twist` of the
original finite representation by the finite determinant character.
`determinantTwistCompactEquiv` gives the corresponding equivalence for the
standard infinite compact. Both use the same actual multiplication
equivalence on vectors. Linearity and the previously proved finite and
compact covariance formulas establish their intertwining identities.
The named application formulas identify these maps definitionally with the
original multiplication equivalence.

`determinantTwistFiniteImageEquiv` applies the same comparison to the existing
actual finite form images. It composes the inverse of the scalar twist of the
source image equivalence, the actual finite twist equivalence, and the target
image equivalence. Its application formula states exactly that this composite
sends the represented image of `f` to the represented image of `Mχ f`.

The provenance is direct internal comparison using
`OperatorDeterminantTwist`, `OperatorRealization`, and the published
`Representation.Twist.Definitions`. It reuses the existing scalar-twist
definition and genuine equivariant equivalences. No new original-literature
identification is asserted. This does not construct local components or prove
unramified Satake, weak-association, or spectral compatibility.
