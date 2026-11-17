# Ambient character transport of target-valued standard intertwiners

Author: Worker 359.

This internal transport module continues
`StandardIntertwiningAmbientTwist`. Its provenance is that module's
character-multiplication equivalence and exact weak-integral domain laws,
together with uniqueness of the actual standard integral and the Library's
target-valued construction. It adds no source assertion or analytic estimate.

Fix the same locally compact nonarchimedean group, semidirect decomposition,
closed radical, smooth Levi representation and ambient smooth character.
The character is trivial on both radicals. The integration measure is fixed.
`domainCharacterTwistEquiv` restricts ambient character multiplication to the
actual domains; its source action is twisted by the ambient character.
Both inclusions follow from the domain membership equivalence. The inverse,
linearity, and equivariance follow from the full induced equivalence.

When the Levi is closed, weak-integral uniqueness applies in the original
carrier. The transported original operator satisfies the twisted integral
specification, so `operator_characterTwist` identifies the selected operator
with multiplication of its output at `g` by `χ(g)`.

For a target semidirect decomposition with the same Levi, retain the actual
quotient measure compatibility, two-sided regular Haar measures on the
target radical and its intersection with the source radical, the ambient
Hausdorff hypothesis, and squared-modulus compatibility required by the
target construction. Equality of underlying functions and the operator law
then prove `targetOperator_characterTwist`. The full-source identity
`fullSourceIntertwiner_characterTwist` follows by including the whole source
in the domain. Its only full-convergence premise concerns the original
representation; convergence for the restricted character twist is proved by
`domain_eq_top_characterTwist_iff`.

The ambient group and representation carrier universes remain independent.
This module does not establish rational continuation, canonical scalar
invariance, rank-one factorization, or unitary inverse regularity.
