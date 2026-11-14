# Coroot preservation for geometric torus factorizations

Worker 235. This internal construction supports the induced-map obligation in
KP Lemma 11.3.6. It derives its claims from the Library's actual derived-cover
lift and the pullback definition of the full preimage torus. It works over
every field extension, without requiring a separable closure.

For each geometric torus factorization of the given group homomorphism,
`geometricPreimageMap` restricts the base change of the lifted homomorphism
on the simply connected covers to the actual preimage tori. The pullback
universal property applies because the cover lift commutes with the ambient
homomorphism and the given torus restriction commutes with the inclusions.
The second projection identity is `geometricPreimageMap_comp`.

Postcomposition defines `torusLatticeMap`. The projection identity shows that
every image of a source preimage-torus cocharacter maps to an image of a target
preimage-torus cocharacter. Thus `torusLatticeMap_corootImage` permits descent to
the integral quotient homomorphism `factorizationMap`. Its effect on every
quotient representative is `factorizationMap_projection`.

This module constructs the map for a single factorization. Independence of
factorization and compatibility with presentation changes are separate
obligations.
