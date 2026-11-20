# Scalar local slices of smooth adelic block sections

At a real or complex place \(v\), let \(\iota_v\) insert a local matrix in
the full adelic matrix group with identity at all other places.
`realPlaceSlice` and `complexPlaceSlice` send a smooth section \(f\) to the
local function \(h \mapsto \ell(f(y\,\iota_v(h)))\), for a fixed adelic point
\(y\) and a continuous complex-linear coefficient functional \(\ell\).
Both are complex-linear maps. The finite coordinate of \(y\) remains fixed
throughout the slice.

In mixed archimedean coordinates, insertion is affine on matrices. Its
constant part places the identity in the other coordinates, and its
real-linear part inserts the tangent into the chosen coordinate with zero
elsewhere. The proof uses the affine formula and the smooth open units chart
to show that the slice is smooth. At a complex place the tangent is an
arbitrary complex matrix in its underlying real vector space.

The slice carries the standard compact translation to actual right
translation by the corresponding local orthogonal or unitary matrix. For the
Lie comparison, extend the orbit expression near the local identity to
ambient matrices using the affine insertion, then apply the real Fréchet
chain rule. The linear part is the published real Lie inclusion at \(v\).
The units-chart formula `mfderiv_eq_fderiv_of_eq_comp` identifies the derivative
with `Archimedean.rightDerivative` used by the Library's standard modules.
The comparison with the derivative on adelic sections retains continuity of
the fixed normalized parabolic operators, as required by `realLieAction`.

The construction uses the group embeddings in
[`ArchimedeanPlaces`](RankinSelberg/ArchimedeanPlaces.md), the real tangent
insertions and compact coordinate formulas in
[`CuspidalArchimedeanGenericComponentReduction`](../Automorphic/CuspidalArchimedeanGenericComponentReduction.md),
and the right action on
[`AdelicParabolicInductionArchimedean`](AdelicParabolicInductionArchimedean.md).
It gives the pointwise compact and Lie comparisons for restricting normalized
adelic induction to a single archimedean place.
