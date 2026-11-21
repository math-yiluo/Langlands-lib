# Isolating a rational norm pair on the norm-one groups

`adelicOrbitIsolation` proves `AdelicOrbitIsolationStatement` for a
cyclic extension of number fields and a supplied split auxiliary
finite place. The selected rational points are norm associated
and the base point is regular semisimple. The compact broad bound
downstairs has regular elliptic finite component at the split
place. The norms of points in the upper broad bound have regular
elliptic component at the supplied finite place upstairs.
The proposition produces matching split auxiliary tests and isolates
the selected ordinary and twisted rational classes for every
function supported inside the respective broad bound and subject
to the selected finite-place support restriction.

The proof obtains a common finite list for the ordinary side by
transporting the compact bound to adelic matrices and using
`generalLinearEllipticClassFiniteness`. It uses
`adelicRationalTwistedFiniteness` upstairs, from the explicit
premise `GeneralLinearWeilAdelicTwistStatement`. Both lists are
chosen before the local support is refined.
`finitePlaceOrbitIsolation` gives the split tests for these lists.
A nonzero global orbit value must come from one of the listed
classes. The corresponding local orbit gives rational conjugacy
to the chosen point by the split test. The genuine rational
norm-one embedding carries that rational conjugator back into
the global group. The proof uses the identity twist on the
ordinary side and `normOneAut` on the upper side.

The split tensor is one at the localized upper point, and the
convolution is positive at its ordered product. The supplied open
neighbourhoods contain that tuple and its ordered product,
respectively. `IsSplitProductHaar` makes the upper ambient Haar
the product of the lower Haar in split coordinates.
For positive-torus averages of adelic tests, the support
conditions on the average can be obtained using
`positiveAverageOrbitSupport` and a broad bound on the original
test.

This is an internal proof of the support isolation used in
Arthur–Clozel, Chapter 1, pp. 43 and 46, and Henniart–Lemaire,
I.6.8, pp. 49–50 (PDF pp. 57–58), in the Library's exact
norm-one group convention.
