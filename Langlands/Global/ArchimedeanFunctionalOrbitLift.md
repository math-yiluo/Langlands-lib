# Smooth scalar lifts of derivative-continuous Hilbert evaluations

Let `F` be a number field and let `π` be a supplied action of the mixed
archimedean general linear group `ArchimedeanGL F n` by bounded complex
linear operators on a complex Hilbert space. Assume that every `π g`
preserves the inner product and that the genuine smooth vectors are dense
in the Hilbert norm. The supplied complex-linear functional `L` on those
smooth vectors satisfies `IsContinuousOnSmoothVectors`: its absolute value
is bounded by a constant times a finite sum of norms of genuine iterated
Lie derivatives.

`functionalOrbitLift` is complex-linear in the smooth vector `w`. Its exact
value at an infinite adelic point `a` (`functionalOrbitLift_apply`) is
`L (π(g) w)`, where `g` is the mixed matrix coordinate of `a` and `π(g) w`
is regarded as a genuine smooth vector. The smoothness and derivative of
this evaluation are the two parts of
`SmoothFunctionalOrbit.contMDiff_mfderiv_smoothFunctional_orbit`, which
uses the unitarity, density and derivative-continuity assumptions. The
published units calculation identifies the invariant tangent at `g` in
direction `Z` with the matrix `g * Z`, the derivative of the left
translation `h ↦ g * h` at the identity. Thus
`smoothDifferential_functionalOrbitLift` identifies the real differential
of the lift in direction `X` with the lift of the genuine derived vector
in direction `realLieAlgebraToMatrix F n X`.

For a supplied complex enveloping action `D` on an original complex vector
space `V` and a complex-linear map `j : V → V∞` into the genuine smooth
vectors, suppose that `j` sends the action of each complexified real
generator to the corresponding genuine derivative. Then
`functionalOrbitLift_envelopingAction` proves that the composite of `j`
with the lift intertwines `D` with the Library's action on smooth functions
for every complex enveloping operator. The proof uses
`envelopingCovariance_of_realGenerators`. That lemma reduces covariance of
any complex-linear map into smooth functions to the unit, sums, complex
scalars and left multiplication by a real generator.

This is an internal specialization of the genuine smooth Hilbert orbit
identity. It does not construct the action, the functional or the map `j`.
