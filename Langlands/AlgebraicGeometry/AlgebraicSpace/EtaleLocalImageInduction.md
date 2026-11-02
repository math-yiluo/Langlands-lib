# Finite field-fibre induction for local chart images

This derived intermediate helper formalizes the induction in the registered
Stacks Lemma 67.50.1 (Tag 03XW), `03XW.html:201-215`, specialized to a
monomorphic map of actual fppf sheaves to a scheme. It works over an arbitrary
base scheme in an arbitrary universe.

`CompactImageDescent S` explicitly isolates the remaining effective descent
step: a compact scheme representing the inverse image of the local chart
image implies a compact scheme representing that image. This interface is
an assumption of the induction theorem, not a proved descent result.

`of_hasFieldFibreBound` proves the conditional induction. A fibre bound at
most one makes the etale base morphism open, so composition with the given
compact open chart represents the image. For a larger bound the actual
off-diagonal projection reduces it by one. `OffDiagonalImageChart` supplies
the recursive affine source, open chart and locally finite type composite.
The induction hypothesis represents its local image. `CompactLocalImage`
glues this with the original chart, and `EtaleImageSaturation.saturation_eq`
identifies that union with the inverse image of the image being sought.
Only at this point does the explicitly assumed descent step apply.

`of_affine_etale` supplies the finite bound using the independently developed
affine etale point bound. No surjectivity of the base etale morphism is
assumed. The module does not prove effective descent or the unconditional
schemehood theorem; those require a proved instance of the stated interface.
