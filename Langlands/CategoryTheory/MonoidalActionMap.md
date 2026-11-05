# Images of internal actions under monoidal functors

This internal construction transports an actual module object along a lax
monoidal functor. The action map is the lax tensor comparison followed by the
image of the original action map. The unit and associativity equations follow
from monoidal coherence and the original action equations. Its acting monoid
is the existing Mathlib image monoid, with no replacement group structure.

This is a derived categorical prerequisite for base changing the actual torsor
in the complete-ring lifting step of the integral Iwasawa proof. The proof uses
the same monoidal coherence pattern as Mathlib's `Functor.monObjObj`; it is not
a new theorem about arithmetic integral models.

For a monoidal functor between Cartesian monoidal categories, the actual shear
`(m, x) ↦ (m • x, x)` of the image action equals the image of the original
shear, composed on either side with the canonical product comparison
isomorphisms. Equality is checked using the two product projections. The
construction therefore preserves invertibility of this shear. No assertion of
flatness, surjectivity, quasi-compactness or the existence of a torsor point is
part of this categorical module.
