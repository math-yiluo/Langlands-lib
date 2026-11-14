# Finite homomorphisms between equal-dimensional smooth groups

This internal derived lemma concerns smooth connected affine group schemes over
an arbitrary field. A finite homomorphism whose source and target have equal
actual Lie finrank is finite, flat and surjective. The actual differential need
not be an isomorphism, and the kernel may be nonreduced.

The implemented proof uses the published actual schematic-image factorization.
Its projection is flat and surjective and is finite because its composite with
the closed image inclusion is finite. The published flat, locally quasi-finite
comparison identifies the Lie finrank of the image with that of the source.
The target has a constant smooth relative dimension equal to its Lie finrank.
The image therefore has at least this topological dimension. The published
full-dimension closed-immersion criterion makes the image inclusion surjective.
It is an isomorphism because the target is reduced, so composing it with the
image projection proves the desired flatness and surjectivity.

This is a supporting geometric consequence of existing Library results, developed
for restrictions of split isogenies to actual root subgroups. It introduces no
isogeny existence assertion or separability hypothesis.

`imageIsoOfFiniteFinrankEq` retains the resulting isomorphism from the canonical
schematic-image group to the target group. Its forward homomorphism is exactly
the canonical closed image inclusion, as the accompanying equality proves. The
construction uses the surjectivity just established, reflects the isomorphism
from schemes to the over category, and lifts it to group objects.
