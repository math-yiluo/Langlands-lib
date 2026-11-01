# Equivariant locally constant descent through original domain spectra

Worker 56 constructs an isomorphism of continuous group actions for locally
constant descent through the original structural quotient of an actual
invariant represented domain. The inputs are an actual positive-polyradius
`PresentedAffinoidAlgebra` over a complete ultrametric normed field, its
`DomainSpectralAction` of a topological group `G`, an open subgroup `H`,
an `H`-invariant represented domain `d`, and an arbitrary coefficient set
`A` in an independent universe. The subgroup retains its original subspace
topology and the coefficients have no topology or action.

`invariantStructuralQuotient_equivariant` exposes the original pointwise
structural equivariance equation. It follows by evaluating the already
constructed equivariant structural morphism. The spectrum action is the
original inverse-pullback action on the entire representing spectrum;
the locus action is the restriction of the ambient action.

`invariantSpectrumFiberLocallyConstantAction` consists of all locally
constant functions on the original representing spectrum that have equal
values on every pair of points with the same `spectrumToLocus` image.
The function subtype has its inherited discrete topology, and its
operator sends `f` to `x ↦ f(g⁻¹ • x)`. Original structural equivariance
preserves these complete fiber equations. Compactness and the already
proved joint continuity on all discrete spectrum functions give joint
continuity on the subtype. The constructed
`invariantSpectrumFiberLocallyConstantInclusion` is the unchanged subtype
inclusion into the full spectrum-function action.

`invariantLocallyConstantDescentIso` is an isomorphism in
`ContAction TopCat H` from the locus-function action to this entire
fiber-compatible spectrum-function action. Its forward map is the
original structural pullback. Its inverse applies the previously
constructed locally constant quotient descent to the original map and
fiber equations. At `spectrumToLocus x` its value is `f x`.
Surjectivity and these evaluations prove both inverse laws; the original
quotient topology proves local constancy. Equivariance at the inverse
group element proves forward equivariance, and the categorical
isomorphism construction derives inverse equivariance. Both maps between
the discrete function spaces are continuous.

The final composition identity proves that this isomorphism followed by
the subtype inclusion is exactly the earlier
`invariantLocallyConstantActionPullback`. Thus the new construction
identifies precisely which original spectrum functions descend; it does
not identify the spectrum with the represented locus.

This is an internal consequence of the existing actual compact geometric
actions, original structural quotient, locally constant quotient descent
and the generic companion `LocallyConstantQuotientAction`. It retains
arbitrary closed ideals, nilpotents, positive polyradii, trivial valuations
and empty loci or spectra. It constructs local constant-coefficient
function data; arbitrary equivariant sheaf descent, analytic site
comparison and the Harris tower remain separate obligations.
