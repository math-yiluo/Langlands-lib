# Self-normalization of a field parabolic complement

This internal consequence of published dynamic structure theory concerns a
connected reductive group over an arbitrary field, a parabolic subgroup, its
supplied ground-field unipotent radical, and a complement whose multiplication
with that radical is an isomorphism. The complement is self-normalizing as a
subgroup functor on all test schemes over the field.

`fieldNormalizerPointsEquiv` constructs the resulting multiplicative equivalence
from normalizer points to complement points. The forward map takes the Levi
component supplied by the multiplication isomorphism; the inverse is the
original complement inclusion.

The proof chooses a dynamic presentation of the parabolic by `parabolicDynamic`.
The actual multiplication isomorphism and radical normality give the retraction
`leviRetraction`. The radical comparison in `OriginalLeviCocharacter` identifies
its kernel with the dynamic unipotent subgroup. The cocharacter conjugacy
theorem then moves the presenting cocharacter into the supplied section, and
`DynamicLeviConjugacy.normalizer_eq_range_of_retraction` proves the assertion.

This is a derived algebraic helper. It assumes no reductivity of the complement
and makes no claim about transporting a relative radical to a field fibre.
