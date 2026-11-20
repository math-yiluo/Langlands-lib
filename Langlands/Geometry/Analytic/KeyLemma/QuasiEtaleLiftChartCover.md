# Lift charts through a quasi-étale factorization

Author: Worker 786.

This module transports the local chart construction in Berkovich's nearby
lifting argument (*Vanishing cycles for formal schemes*, 1994, §7) from
étale maps to quasi-étale charts. A bounded map with spectral lifts
retains the property after restriction to a represented affinoid domain,
by spectral test transfer. Spectral lifts also descend through a bounded
representation of the whole spectrum.

A local domain–étale factorization has a common strong refinement
of its original chart and its domain in an étale envelope. The
pullback out of an envelope chart represents a domain on a chart of
the refinement. The pullback out of the image chart in the original
source represents the whole spectrum. Apply the two transfer rules to
the pullback square to obtain spectral lifts on the original chart.

For each original chart with a domain–étale factorization, pull the
étale envelope's local lift-chart cover back to the common refinement.
Compactness of the original chart and the homeomorphism from the
refinement give a finite subcover. The transported lift charts cover
the original chart. Applying this to the finitely many charts in the
quasi-étale cover gives a finite cover of the whole source.

`HasFiniteLiftChartCover` records that the ranges of these lift charts
locally refine the whole source. Since the source is Hausdorff, the
chart ranges are closed. At each point the complement of the union
of the finitely many chart ranges missing that point is a
neighborhood covered by the charts containing it.
