# Transport of formal idempotent images

The proof of Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), Lemma 6.44, printed pp. 309–310 (PDF pp. 321–322), uses relative Frobenius on the first summand of the split object and then identifies the resulting object over the twisted coefficient ring.

`Hom.IdempotentImage.transport` composes an existing inclusion with the ambient coordinate isomorphism and composes the inverse coordinate isomorphism with the projection. This transports the image to the conjugate projector. If an ambient rational section is also conjugated, the comparisons cancel when it is restricted to the two transported images.

`Hom.frobeniusHom_natural` applies the naturality of the actual variable-power map to the coordinate series of a formal homomorphism. Applied to the inclusion of an image, this gives `restrictHom_frobeniusHom`. The projected relative Frobenius equals the actual relative Frobenius of the image law. The proof uses the retraction identity after coefficient Frobenius.
