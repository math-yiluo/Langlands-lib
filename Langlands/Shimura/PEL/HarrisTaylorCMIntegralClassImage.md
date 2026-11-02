# The exact normalized CM image of integral-action representatives

This internal construction uses the existing normalized Harris polarized
representatives, their original invariant adelic level orbits and the existing
normalized determinant-and-dimension condition. It adds a supplied action of the
actual Harris integral order on the same abelian scheme, agreeing with the
original rational action. All tensor, Picard, dual geometry, polarization,
additivity, torsion, Weil and adelic inputs remain explicit. The positive
auxiliary left involution, opposite right-action transporter convention and
conjugated reflex scalar map are unchanged.

`IntegralCMRepresentative` records precisely this data. The map
`integralCMRepresentativeClass` forgets the integral action into the original
normalized CM class. `IntegralCMRelated` is the explicit existential relation
using an original rational action isomorphism, an original rational unit
multiplier, exact integral equivariance and polarization witnesses, and the
original invariant level-orbit equation. It does not use arbitrary integral
isomorphisms or a different orbit relation. The imported same-representative
integral criterion proves that this relation is equivalent to equality of the
original normalized classes. Consequently it is an equivalence relation,
including when different supplied integral lifts have the same rational image.

`IntegralCMIsoClass` is the quotient by this relation. Its forgetful map into the
original classes is injective. `IntegralCMClassCondition` means that a class
admits an actual representative with the displayed integral action, and
`IntegralCMClassImage` is the corresponding subtype of the original classes.
`integralCMClassImageEquiv` identifies the quotient with exactly this image.
The forward map is the original normalized class of the same representative;
the inverse is obtained from the proved surjectivity onto the image by classical
choice. No canonicity of a representative or integral lift is asserted.

Every original Harris level transporter preserves the underlying polarized
object, normalized condition and integral action and changes only its adelic
orbit. The construction therefore defines the quotient tower and the image
tower on the entire original level category. The quotient-to-image equivalence
is a natural isomorphism, and the image includes naturally into the original
normalized class tower. The proof of functoriality uses injectivity of the
forgetful map and the already proved functoriality of that original tower.

The image need not be the entire original moduli set by anything proved here.
In particular the construction does not assert that an arbitrary rational
order action lifts on its original abelian scheme or has an isogenous integral
model. It proves no ordinary moduli existence, smoothness, projectivity,
admissibility or representability. The provenance is the internal application
of the imported exact integral-witness criterion to a quotient and its actual
image, followed by the existing original level transporter action.
