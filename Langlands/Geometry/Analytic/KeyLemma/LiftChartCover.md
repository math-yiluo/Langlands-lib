# Local covers by charts with nearby lifts and rigidity

Author: Worker 786.

This module supplies the local étale chart cover for the nearby-lift
argument of Berkovich, *Vanishing cycles for formal schemes* (1994),
§7, Key Lemma 7.2. It uses spectral test transfer on represented
affinoid domains, obtained by applying the rational-chart result to
the finite rational cover reduction.

`IsSpectralLiftChart` asks for spectral lifts along the bounded
pullback of the chart, over all points of its spectrum. It implies
`IsLiftChart` by the pullback formula for a composite of strong maps.
The algebra-level property allows chart comparison under bounded
algebra equivalences.

For a source chart in a recognized finite affinoid piece, first
transfer finite tests on the chart to tests on that piece. The
Laurent lifting property produces a close map out of the piece.
Test transfer then factors this map through the chart algebra.
The equality of composites with the base map follows from the
chart pullback square and surjectivity of the bounded restriction
from the recognized target piece onto the target chart.

At an étale point use a joint flat and unramified witness to choose
finite affinoid pieces over finitely many target charts. Inside each
source piece, restrict near the point to the Laurent lifting locus
and to a positive lower bound for an element of the annihilator
of the module of differentials. The resulting local cover within
the requested analytic domain has both properties. Nearby lifts
come from the Laurent lifting property and the chart argument.
Rigidity follows from the lower bound and the existing unramified
rigid-chart lemma.
