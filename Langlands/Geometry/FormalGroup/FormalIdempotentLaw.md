# The formal group law on an idempotent image

The split pair of Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), (6.17), printed p. 309 (PDF p. 321), uses the images of the two order idempotents as formal groups. This module constructs the group law once the image has pointed coordinate inclusion and projection.

`CoordinateMap.IdempotentCoordinates.imageLaw` includes the two inputs, adds them using the ambient formal law, and projects the sum. It restricts inversion by the same procedure. Inclusion is injective and identifies these operations with the ambient ones because the included points are fixed by the projector. The group-law identities follow on series points and hence on the actual coordinate maps. The inclusion and projection preserve addition, and their composites recover the identity and the given formal endomorphism.

For a formal module endomorphism the scalar maps commute with the projector. Restricting them along the inclusion and projection gives a unital ring action. Differentiating the restricted scalar map gives multiplication by the structural scalar because the derivative of inclusion followed by projection is the identity. Both maps are formal module homomorphisms. `ModuleLaw.Hom.IdempotentImage.ofTangentRetraction` combines this construction with the pointed retraction from a finite free presentation of the tangent image.
