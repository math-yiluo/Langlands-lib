# Formal idempotent images on principal opens

The two summands in the split polarized object of Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), §6.43 and (6.17), printed pp. 308–309 (PDF pp. 320–321), can be treated in local finite coordinates. This module constructs those coordinates for an actual formal idempotent on an affine coefficient ring.

The tangent image is the range of the actual tangent projector. The range inclusion and the range restriction of the projector exhibit it as a direct summand of the finite free coordinate module, so it is finite projective. Coefficient extension of the formal tangent is matrix coefficient extension, which is the tensor extension under the finite coordinate basis comparison. Thus a basis of the scalar extension of the tangent image gives the two linear maps needed to construct the image law.

At every prime, finite projectivity supplies a free tangent image over the local ring. Finite presentation gives a principal open containing the prime where the localized image has a basis. `Hom.IdempotentImage.exists_basicOpen` uses that basis and the previously constructed formal retraction to obtain an actual formal module law and its integral inclusion and projection on the chosen open.
