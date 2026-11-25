# Open descent and local geometry of full Isom schemes

This is internal derived material from the published fppf sheaf
property of full `LocalGroupIso` families, change-of-base equivalences, and
scheme representation gluing over open covers.

`GroupIsomorphismScheme.ofOpenCover` constructs a full Isom representative
from full representatives of the pulled-back groups over a base open cover.
The local representatives identify with restrictions of the original full
Isom presheaf. The existing scheme gluing theorem applies because that
presheaf is an fppf sheaf. Its resulting natural representation supplies
the universal all-test local isomorphism and its classification bijections.

`localParameterIso` identifies the actual pullback of any supplied global
representative with any supplied local representative. Full faithfulness
of the scheme Yoneda functor and the change-of-base presheaf equivalence
produce the isomorphism. Accordingly any morphism property local at the
Zariski target transfers from the local representatives on an open cover
to the global representative. A property stable under base change and
satisfying fppf target descent transfers along any étale covering family
as well. The latter proof views the étale cover as an fppf cover and uses
the same parameter isomorphisms on its actual scheme pullbacks.

No scheme representative is descended along an arbitrary étale cover in
this module: only its structural morphism properties are checked there.
Representability is constructed only along the given open cover. All
universe levels and arbitrary scheme-valued tests are retained, without
a connectedness, affineness, or finite-cover assumption.
