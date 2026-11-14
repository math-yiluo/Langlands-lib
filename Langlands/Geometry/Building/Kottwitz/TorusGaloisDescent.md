# Galois compatibility of torus norm squares

These internal lemmas implement the Galois compatibility used in the proof of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.1.1,
printed pp. 421–422 / PDF pp. 452–453. They adapt the existing actual coefficient
point, splitting-field and integer valuation constructions.

Conjugation by an automorphism over the ground field permutes automorphisms
fixing a normal intermediate field. Applying the injective extension of points
reduces compatibility of the relative norm to reindexing its Galois product by
this permutation.

A ground-field automorphism preserves the restricted spectral valuation, by
invariance of the spectral norm after extension to the separable closure. The
selected integer valuation has the same comparison relation as the restricted
spectral valuation, so it has equal values on conjugates. The source-positive
integer orders of units are consequently equal as well.

On pure coefficient evaluations, the existing Galois tensor formula transports
both the unit and the cocharacter. The integer order of the unit is unchanged
by the preceding valuation result. The cocharacter extension intertwines
compatible automorphisms of the splitting field and the separable closure;
projection to inertia coinvariants then gives the residual Galois action.
Additive extensionality on pure evaluations extends this identity to every
coefficient point. These arguments give `normLawValue_groundConjugate_tmul`
and `normLawValue_groundConjugate`.

Finally, `torusKottwitzEquivariant_of_normal_splitting` applies the selected
Kottwitz map's norm law at a finite Galois splitting field L/K normal over F.
Lift an automorphism of K/F to the separable closure, then restrict it to L.
The restrictions agree on K. Every K-point is a relative norm from L, by
`relativeNorm_unramifiedClosure_surjective`. On such a norm, compatibility of
the relative point norm and of `normLawValue` proves the desired equivariance.
The theorem is conditional only on the supplied splitting field, whose
existence is provided separately by `TorusGaloisSplitting`.
