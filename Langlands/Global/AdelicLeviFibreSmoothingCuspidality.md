# Constant terms of smoothed families of cuspidal Levi classes

Fix a standard parabolic \(P=MU\) in a compatible standard family over
a number field. Use the positive split torus, quotient measure and
right-invariant norm-one Haar of `leviFibreSmoothing`. For a compactly
supported continuous ambient kernel \(\beta\) and a continuous family of
classes in the full cuspidal \(L^2\) subspace of the positive rational
quotient of \(M\), `isCuspidalAlong_leviFibreSmoothing` proves that the
smoothed function has zero constant terms along every standard \(Q<P\).

For such a \(Q\), restrict the common maximal split torus to \(M\). Its
simple roots are the subset indexing \(P\). The subset indexing \(Q\)
defines a proper standard parabolic in \(M\) by the standard parabolic
order theorem. The closed affine dynamic decomposition represents this
parabolic and its geometric unipotent radical. The restriction of the
standard families identifies that radical with \(U_Q\cap M\) on all
test schemes. The period comparison `subgroupConstantTerm_leviFibre`
then reads the ambient \(Q\) constant term as the period of the Levi
fibre at the identity.

The rational quotient of the represented Levi radical is compact, so
its adelic points lie in \(M(\mathbb A)^1\). The norm-one covariance
of `leviFibreSmoothingIntegrand` moves the radical point from the
ambient translate to the evaluation argument of the partial
convolution. Rational invariance gives a continuous integrand on the
product of the compact radical quotient and the positive subgroup.
The positive variable has compact support uniformly in the radical
point. Fubini moves the radical integral inside the positive integral.
For each positive point, the assumed cuspidal class has partial
convolution with zero proper constant terms, so this inner integral
vanishes.

`isCuspidalAlong_finiteLeviFibreProjection` applies the result to the
finite family of cusp vectors. Each constant term is integrable by
continuity and rational unipotent invariance on a compact radical
quotient. Linearity gives vanishing for the finite weighted sum.

This proves the relative cuspidality of the smoothing construction
used for the projection characterized by Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §6.2,
equation (6.8). The radical periods use the volume-one convention
of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.1.13.
