# Controlled finite recognized chart pairs

This internal construction selects finite full-recognition pairs at prescribed
points. The coefficient field is a complete ultrametric normed field. Its
universe, the ambient space universe, and the original atlas index universe
remain independent.

A rational neighborhood in the spectrum of a prescribed target chart gives a
recognized local domain containing the image point and lying inside any given
ambient neighborhood and that chart. The target chart itself need not be an
ambient neighborhood. No such neighborhood property is inferred.

`HasAllPiecesAt.exists_pointed_fullRecognitionPair_within` first uses
`HasAllPiecesAt.exists_small` to shrink a finite source neighborhood into a
prescribed source neighborhood, retaining a property stable under flat
surjective source restrictions. It then chooses the target rational piece
inside the finite target neighborhood and a prescribed target neighborhood.
The defining finite-over certificate supplies a recognized preimage. A spectrum
point of that preimage is chosen to chart to the prescribed source point, and
the universal all-pieces property supplies the property at that exact point.
The resulting source locus lies in the prescribed source neighborhood; the
target locus lies in both the prescribed target chart and target neighborhood.

The pointwise etale specialization combines the flat and unramified all-pieces
certificates at the source point. Flat surjective source restrictions are flat
and formally unramified. Their composition with the finite piece retains the
two pointwise properties. Thus the selected finite bounded map is etale at the
specified source spectrum point.

`exists_pointed_fullRecognitionPair_over` uses the actual strong map to the
full-recognition target to find a source chart through a prescribed second
point over the same recognized target. Intersecting with a prescribed source
chart retains that point. Recognizing this chart gives the second source
piece, with its complete bounded pullback. The final lemma uses injectivity of
the recognized target chart and the two actual chart-commutativity identities
to show equality of the two comap images in the actual target spectrum.

These are derived consequences of the existing rational-neighborhood,
finite-over, all-pieces restriction and strong-map chart APIs; no external
statement is transcribed. The conclusions concern recognized affinoid pieces,
which may comprise several original local domains. They do not assert that a
finite recognized source piece is a single original chart, construct a global
pullback, or prove etale base change. Those lie outside this module.

`ControlledFiniteEtalePairsStatement` quantifies these choices for both actual
strong maps, the two prescribed ambient points with equal image, a source
neighborhood for the finite leg, a target original chart and neighborhood, and
a saturated source chart for the second leg. `controlledFiniteEtalePairs`
combines the selectors and chart identities to prove that proposition. Only
the first bounded map is asserted finite and etale at its chosen point. The
second piece has its prescribed chart containment, without a finiteness
assertion. This proposition makes no claim that ordinary point pairs detect
arrows or distinguish global pullback points.
