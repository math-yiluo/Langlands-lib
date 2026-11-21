# Actual automorphic quotients from projected Eisenstein specializations

`compactProjectionSeed` is a basis of the finite-dimensional projection range viewed in the inducing carrier. `exists_automorphic_subquotient_of_compact_projected_seeds` takes an operator family, an input simple quotient at the specialization, and the compact projection data. The prescribed nonzero target vector lifts to the projection range and makes specialization from the free seed module surjective.

The continued seed family gives one normalization ball and a complex line through the specialization and an injective regular parameter. For a word over the prescribed target vector, the proof uses one algebra element to project its entire section family. The projected section has entire basis coordinates and a nonzero specialization. The normalized operator identity compares this section curve with the word's Taylor coefficients near the specialization. The cyclic lift test then constructs one actual irreducible automorphic operator subquotient and identifies its finite action with the supplied target action.

This conditional extraction implements the normalization, parameter derivatives and compact-type detection in Langlands' proof of Proposition 2, printed pp. 205–207 (Corvallis Part I PDF pp. 200–202). It uses supplied continuation, regular injectivity and open operator identities on the finite seed family.

`exists_freeOperatorQuotient_of_compact_projected_seeds` concludes with a surjection from an invariant numerator of stable automorphic functions, linear for every free operator. The corollary descends it to the concrete operator algebra and identifies its finite representation.
