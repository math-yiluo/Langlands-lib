# Smooth scheme representations of actual relative automorphisms

This internal interface is built from the actual scheme pullbacks and the
published scalar-automorphism comparison. It does not assert a representability
or smoothness existence theorem.

Let `f : X ⟶ S` and `T : Over S`. The functor `sliceToBundleBase f T`
sends a scheme `Z ⟶ T.left` to the actual scheme `Z ×_S X` with its induced
map to `T.left ×_S X`. It first identifies this test with an object of the
iterated slice and then applies `Over.post (relativeSpace f)`. Thus its maps
are precisely those induced by the published functor `relativeSpace f`.

For an actual line bundle `L` on `T.left ×_S X`,
`sliceAutomorphismPresheaf f T L` takes the automorphisms of its ordinary
pullbacks along these induced maps. It uses
`PicardGroupoid.pseudofunctor.presheafHom`, including that construction's
composition comparisons, and lifts its values from `Type u` to
`Type (u + 1)`. Automorphisms are retained as data. Tests range over the
entire category `Over T.left`.

`sliceUnitsAutomorphismPresheafIso` identifies this presheaf with
`(Over.map T.hom).op ⋙ RelativeGlobalUnits.presheaf f`. At every test its
component is the published equivalence from global units on `Z ×_S X`
to scalar automorphisms of the same pulled-back bundle. Its naturality
is inherited by whiskering `unitsAutomorphismPresheafIso`; the intervening
identification of the two unit presheaves has identity components and
identical restriction maps. This avoids choosing new identifications of
iterated fibre products.

`HasSmoothAutomorphismSchemes f` quantifies over every relative test and
every actual bundle on it. For each bundle it requires a scheme over the
test, an isomorphism of full presheaves from its lifted Yoneda presheaf
to the actual automorphism presheaf, and ordinary scheme smoothness over
the test. `HasSmoothUnitSchemes f` imposes the same condition on the
relative-unit presheaf restricted to every slice.

The implemented forward implication composes any unit representation with
the scalar comparison, retaining its scheme and smoothness proof. The
converse applies the automorphism condition to the actual trivial bundle
and composes with the inverse comparison. Hence the two predicates are
equivalent without any extra assumption on `f`.

This contribution supplies the condition needed by a future smooth-inertia
quotient argument. It proves neither that these conditions hold for proper
schemes over fields nor that a sheaf of isomorphism classes is algebraic.
It also does not assert a comparison with `presheafHom` formed directly
from the relative pseudofunctor; any argument using that presentation must
establish the comparison with the ordinary pullbacks used here.
