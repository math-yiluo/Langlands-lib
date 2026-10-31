# Actual determinant twists of full automorphic operator realizations

Author: Worker 2. This internal construction works over every number field
`F : Type u` with complex coefficients and every natural rank. It starts
from the existing actual full `OperatorRealization` and the proved
finite-order determinant multiplier on the existing stable operator core.

`OperatorRealization.determinantTwist` is the image of the original
invariant subspace under actual multiplication. The whole-algebra covariance
identity proves that every concrete operator preserves this image: its
pullback by multiplication is another element of the same algebra.
`determinantTwistEquiv` is the inherited continuous complex-linear
equivalence from the original space to that image.

The whole-algebra formula identifies the action on the image with the
original action precomposed by the actual determinant conjugation
automorphism. The finite and standard infinite compact formulas carry
the original determinant-character scalar, and the whole enveloping
differential action is unchanged. The map into continuous functions is
exactly original determinant multiplication. Consequently the constructed
image and this actual equivalence satisfy all three equations of the
published `DeterminantTwistEquations` and establish the existing
`IsFiniteOrderDeterminantTwist` relation.

`determinantTwistSubrepresentationOrderIso` maps each full invariant
subspace to its image under the equivalence and pulls a target subspace
back by that map. Whole-algebra covariance proves forward invariance.
The inverse conjugation automorphism proves invariance of the preimage.
Mathlib's submodule image/preimage order equivalence supplies the inverse
and order laws. The order equivalence therefore preserves the exact
existing full-operator irreducibility condition in both directions.

With the explicit compactness instance needed by the normalized constant
terms, cuspidality is equivalent before and after twisting. The proof
uses surjectivity onto the actual multiplied image, its exact function
formula, and the published cuspidality equivalence for actual determinant
multiplication.

`CuspidalOperatorRealization.determinantTwist` is a total constructor on the
existing positive-rank irreducible cuspidal realizations. Its
irreducibility and cuspidality fields are the preceding proved preservation
results. It satisfies the existing full finite-order twist relation.
No target realization, intertwining equivalence, or preservation witness
is supplied as an extra input.

The provenance is direct internal image and restriction construction using
`StableAutomorphicDeterminantMultiplier`, `DeterminantOperatorConjugation`,
`OperatorRealization`, `CuspidalOperatorRealization`, and
`FiniteOrderDeterminantTwist`, together with Mathlib's submodule order
equivalence. No new original-literature identification is claimed.
The construction asserts neither existence of nonzero cuspidal input
objects nor equality of the stable core with all automorphic forms.
Descent to isomorphism classes, character action laws, and central-character
transport remain separate.
