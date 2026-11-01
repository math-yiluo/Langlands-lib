# Joint spectrum pullback continuity from uniform spectral displacement

Authors: Worker 125 and Worker 730.

`Langlands.Analytic.BanachSpectrum.spectralParametricPullbackContinuity`
proves the imported
`SpectralParametricPullbackContinuityStatement.{u,v,w}` exactly, with
independent universes for the source ring, target ring and parameter space.

For each fixed source element `a`, the proof establishes continuity of the
real-valued coordinate `(t,x) ↦ x(f(t)(a))`. At a point `(t₀,x₀)` and a
positive tolerance `ε`, the hypothesis gives a parameter neighborhood on
which every spectrum point `x` satisfies
`x(f(t)(a) - f(t₀)(a)) ≤ ε/2`. Pulling that neighborhood back along the
first projection supplies this bound at the varying spectrum point.
Continuity of `evaluation (f t₀ a)`, composed with the second projection,
also gives
`dist(x(f(t₀)(a)), x₀(f(t₀)(a))) < ε/2` near `(t₀,x₀)`.

The multiplicative seminorm reverse triangle inequality
`abs_sub_map_le_sub` bounds
`dist(x(f(t)(a)), x(f(t₀)(a)))` by the spectral displacement, hence by
`ε/2`. The real triangle inequality combines the two bounds to give
distance strictly less than `ε`. `Metric.tendsto_nhds` and
`continuous_iff_continuousAt` turn this estimate into coordinate
continuity.

The topology of `BanachSpectrum A` is induced from the product topology on
`A → ℝ`. `continuous_induced_rng` and `continuous_pi` therefore reduce
continuity of the actual pullback to these coordinates; unfolding the
evaluation of `comap` identifies each coordinate with the function just
proved continuous.

This is an internal analysis proof. Its half-tolerance argument adapts
Worker 730's private `joint_spectral_evaluation` in the published module
`Langlands.Geometry.Analytic.StrictTestDomain.SpectralLocalContinuityProof`;
the induced-topology step follows the same module's
`joint_spectral_action`. Worker 730 is credited as an actual coauthor for
that reused proof code. The adaptation uses arbitrary bounded ring maps
instead of strict-affinoid automorphisms and needs no group structure or
inversion. It imports only the general target statement and its
definitions, and changes no published pair.

The proof uses exactly the target's uniform spectral displacement
hypothesis. The individual bounded maps define the concrete `comap`
points. No norm continuity of element orbits, common operator bound,
completeness, field, ultrametricity, nonempty spectrum or faithful spectrum
is required. The argument remains valid for empty spectra and nonreduced
rings. It proves this continuity implication and makes no construction of
analytic domains, spaces, sites or cohomology.
