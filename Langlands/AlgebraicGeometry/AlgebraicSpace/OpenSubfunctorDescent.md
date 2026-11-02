# Descent of invariant subfunctors

This internal helper supports descent in the scheme-representability proof for
separated commutative group algebraic spaces. It uses the universal image
(right adjoint to inverse image) from the Library's OpenSubfunctorLifting module.

For arbitrary presheaves F and G, a transformation π : F → G, and a subfunctor A
of F, suppose membership in A is constant on every fibre of π at every test
object. Then `universalImage_preimage_eq_of_invariant` states that inverse image
along π of the universal image of A equals A. No sheaf, openness, surjectivity,
or representability hypothesis is needed for this formal assertion.

One inclusion follows from the universal-image adjunction. For the other, take
x in A, an arbitrary restriction of π(x), and an arbitrary lift y of that
restriction. Naturality puts y in the same fibre as the restriction of x.
Invariance and the subfunctor restriction law put y in A, which is the defining
condition for universal image. This is a derived result, with no independent
literature assertion beyond the imported definitions.

The scheme lemmas also identify the universal image of an open immersion
q : W → R along any scheme map p : R → T, on every test U → T. Its points
are exactly the maps U → T whose image avoids p(R \ range(q)). In the forward
direction, a point of a fibre of p over a point of U lifts to a point of the
scheme pullback R ×_T U. The defining universal-image condition factors its
projection to R through W, putting the original point in range(q). Conversely,
avoidance of p(R \ range(q)) forces every such projection to land in range(q),
so the open-immersion factorization criterion gives the required factorization.
No surjectivity, flatness or immersion hypothesis on p is used here.

When p is a closed map on scheme points, the complement of p(R \ range(q))
is open. The definitions `universalOpen`, `universalScheme`, and `universalMap`
construct that open, its actual scheme over S, and its open immersion into T.
The theorem `universalImage_scheme_eq_range` proves equality as subfunctors on
all test schemes, rather than merely equality of sets of geometric points.

For a representable transformation π, `universalImage_open_of_closed` assumes
that every represented projection is topologically closed. It then proves that
the universal image of any representable open subfunctor is again a
representable open subfunctor. The proof pulls the given open back to each
scheme test, applies the preceding construction, and uses the Library's
pullback compatibility of universal image to identify the resulting open.
The theorem `universalImage_open_of_finite` obtains the closed-map hypothesis
from finiteness of every represented projection. The base S is arbitrary.
These are derived results from the Library's universal-image construction and
Mathlib's scheme pullback point-surjectivity and finite-morphism API.
