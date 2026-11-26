# The degree of a doubled polarization on a connected base

Let \(A\) be an abelian scheme over a connected locally noetherian
scheme and let \(\lambda\) be a polarization into its chosen dual
as in `DualWitness.IsPolarization`. At a supplied algebraically closed
point of characteristic zero, `DualWitness.doubledDegreeIndex` gives
a positive integer \(d\). At every point of the original dual,
the native finite flat rank of \(2\lambda\) is \(d^2\).

On the indicated geometric fibre, the Poincaré diagonal bundle of
the pulled-back \(\lambda\) is ample by
`poincareDiagonal_isAmple_of_fieldPresentation`. Its Mumford map is
twice the pulled-back polarization by `polarizationDiagonalMumford`.
The map is an isogeny by `GroupScheme.multiplicationIsogeny` and
stability of isogenies under composition. The index is the absolute
value of the Euler characteristic of the diagonal bundle. The
formula `algClosedFieldAmpleMumfordEulerSquare` gives its square as
the native rank. The rank is positive by `isogenyFinrankKernelCard`,
since the geometric point kernel is finite and contains the identity.

The canonical changed dual in `DualWitness.pullbackMap` identifies
this with the scheme-theoretic pullback of the original doubled
map. Native rank is preserved under this pullback by
`Scheme.Hom.finrank_of_isPullback`. The original dual is connected
because it is smooth and geometrically connected over the connected
base. The rank is locally constant by
`isLocallyConstant_finrank_of_isIsogeny`, so its value at the given
geometric fibre determines its value everywhere. The result derives
from the named diagonal and Euler-characteristic results.
