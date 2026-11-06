# Locality of the relative torus property

Author: Worker 1726.

The Library property `RelativeTorus.IsTorus` means that the actual group
scheme becomes a finite split torus on an étale cover; its rank may vary
between cover members. This module proves that this property is detected
on an arbitrary étale cover, and hence on an arbitrary Zariski open cover.
The scheme and the cover index types use an arbitrary universe `u`.

For every member of the given cover, choose the étale splitting cover
supplied by the local torus hypothesis. Bind these covers to obtain one
étale cover of the original base, defined as `IsTorus.splittingCover`.
The canonical group-scheme comparison
between direct and iterated pullback identifies each new pullback with the
corresponding split torus. The open-cover result regards every open
immersion as étale. The final equivalence combines this detection result
with the published preservation of `IsTorus` under arbitrary base change.

This is an internal consequence of the published definition and pullback
comparisons, using Mathlib composition of covers. No assertion about a
moduli scheme or effective gluing is made here.
