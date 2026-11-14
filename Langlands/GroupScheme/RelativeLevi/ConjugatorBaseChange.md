# Range conjugators as conjugacy after base change

This internal construction defines `rangeConjugateAt l T g` to be the actual
pointwise range of the base change of `l`, followed by conjugation by the section
of the base-changed group corresponding to `g : T → P`. It uses the published
pullback equivalence for base points; it requires no field, smoothness,
monomorphism or relative Levi hypothesis.

Its membership criterion follows from the published criterion for a range
followed by an inner automorphism, compatibility of ranges with arbitrary base
change, and the pullback formula for the constant family of a section.
Membership is tested in the original range after inverse conjugation by `g`
restricted along the test scheme's structure map to `T`.

The equivalence with `IsRangeConjugator` treats every further relative test
scheme, including tests with nilpotents. In the forward direction a test over
the scheme underlying `T` supplies a test over the original base and its
structure map to `T`. Conversely, a morphism `a : V → T` over the original
base makes the scheme underlying `V` a test over the scheme underlying `T`.
The point equivalence gives a point of the base-changed group. An isomorphism
with identity underlying scheme map reconciles the two composite structure
maps, and functoriality of subgroup membership transports the resulting
equivalence back to `V`.

This is a categorical comparison for use in the relative Levi conjugacy proof.
It does not construct a conjugator or establish uniqueness.
