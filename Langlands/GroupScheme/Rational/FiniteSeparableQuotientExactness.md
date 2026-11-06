# Finite separable cocycle vanishing and rational quotient lifts

This internal deduction combines actual finite separable local lifts and
the represented-kernel quotient-point obstruction. It is conditional on
kernel-cocycle vanishing and supplies no arithmetic vanishing proof.

Let `F : Type u` be any field and let `n : N → G` and `q : G → Q` be
homomorphisms of actual group schemes over `Spec F`. Assume that the
underlying map of `n` is monic and that its full scheme-valued point
range equals that of the actual kernel inclusion of `q`. Assume that the
underlying scheme map of `q` is smooth and surjective.

`surjective_of_finiteSeparable_vanishing` assumes that every actual
`Cocycle N (Spec L over Spec F)` is trivial, for every finite separable
field extension `L/F` with `L : Type u`. It proves that postcomposition
with `q` is surjective on actual `F`-valued points.

For each target point `y`, `exists_finiteSeparable_quotient_lift` produces
a lift over some finite separable extension. The cover `Spec L → Spec F`
is flat and surjective, and both schemes are affine. Mathlib's
`isRegularEpi_of_flat_of_surjective_of_isAffine` makes it an effective
epimorphism. Apply the vanishing assumption to the actual kernel-valued
obstruction of this local lift. The proved
`QuotientPointCocycle.exists_lift_of_isTrivial` then supplies a lift
over `F`. A single extension need not work for every `y`.

`quotientPointLiftOfFiniteSeparableVanishing` chooses a rational lift
using this surjectivity proof. It returns the actual point together with
its proved quotient-image equation.

The group schemes need not be affine, reductive or simply connected.
The vanishing hypothesis is an explicit additional assumption. No local
field, classification, radical-existence or rational-generation assertion
is proved here. In particular this construction does not prove
`LocalKneserTitsStatement`, nor does it identify a Whitehead quotient
with a quotient of group schemes.
