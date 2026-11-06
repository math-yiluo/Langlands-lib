# One finite-level approximation on the original quotient and full cusp L2 spaces

This internal target uses one decreasing compact open basis of the original
finite adelic point group to approximate the identity on the existing ambient
canonical quotient L2 space and its existing full all-parabolic AE cuspidal
Hilbert submodule. The original measures, null classes, norms, finite actions,
faithful inclusion and orthogonal projections are unchanged.

The sequence is chosen before either vector is quantified. Every subgroup is
open and has compact carrier in the original finite adelic topology, and the
carriers form an antitone identity neighborhood basis. Both averaging operators
are the existing normalized probability Haar Bochner averages over this same
subgroup with its inherited topology. There is no independently chosen cusp
sequence or approximation operator.

The target requires output membership in the existing `Langlands.fixedVectors`
for each respective original finite action and the actual subgroup at that
level. Both averaging sequences must converge strongly to the identity. The
existing `Langlands.IsSmoothVector` set must be dense separately in each
original space. The faithful original inclusion must identify the two averages,
the original subtype-valued orthogonal projection must intertwine them, and the
original ambient cusp projection must commute with the ambient average.

All hypotheses of the original full cusp construction remain: an arbitrary
number field, affine locally finite-type connected reductive group scheme,
the structural `ParabolicDynamicStatement`, supplied finite split central
torus, injective finite-index character restriction and norm-one right-Haar
invariance. Every actual proper rational parabolic still has separate
almost-everywhere absolute convergence and vanishing requirements. No
smoothness, extra closedness or completeness premise is supplied.

Provenance is internal. The ambient finite approximation target supplies the
decreasing compact open basis and its strongly convergent ambient averages.
The existing exact inclusion identity identifies the cusp averages with
ambient averages of cusp vectors. The original isometric subtype inclusion
then transfers convergence to the original cusp norm. Each cusp approximant
is already fixed by the actual subgroup, giving density of the existing
finite smooth-vector set. The existing projection identities supply the
remaining comparisons. This describes a derived target, not a proof in this
statement file.

Finite adelic smooth density is only the conclusion stated here.
Archimedean smoothing, Getz–Hahn 6.1 tensor realization, admissibility,
growth, decay, trace and spectral decomposition remain distinct obligations.
