# Actual cotangent pullback and equivariant weight transport

This derived interface records the functoriality of the augmentation quotient
used with Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
§3.3, printed pp.107–108 / PDF pp.133–134. The source defines the actual
augmentation `I` and its cotangent `I/I²`; the explicit morphism interface and
proof target here are implementation consequences of that construction.

`pullback_augmentationIdeal` proves that an actual group homomorphism preserves
the identity augmentation ideals, by the already proved coordinate-origin
composition law. `cotangentPullback` is the map induced on these precise ideals'
quotients using `Ideal.mapCotangent`. `cotangentPullback_mk` proves its agreement
with the already constructed actual augmentation pullback on every class.
The identity and reversed composition laws are proved by representing each
cotangent class by an augmentation element and applying the coordinate pullback
laws. `cotangentPullbackEquiv` uses the two maps of an actual group-scheme
isomorphism as inverse linear maps. No abstract linear equivalence replaces
the quotient pullback.

`CotangentPullbackStatement` is an unproved proposition target. It asks that
for any actual equivariant group homomorphism, pullback sends each actual
cotangent eigenspace into the eigenspace with the same character. It also asks
that an equivariant group-scheme isomorphism preserves cotangent support.
The eigencondition retains all coefficient algebras and acting points through
`cotangentWeightSpace`; neither splitness nor smoothness is necessary for this
functoriality target. Every universe and field characteristic is retained.

The proved helper maps supply actual cotangent quotients to consumers, while
their compatibility with all-base torus actions remains the explicit focused
proof obligation. This target does not assume semigroup realization,
commutator bounds, or cotangent/Lie-support comparison. It specializes to the
existing action on a represented stable subgroup through its actual representing
inclusion and `represented_inclusion_equivariant`.
