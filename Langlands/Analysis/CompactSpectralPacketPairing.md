# Compact spectral support and packet pairing

For a finite parameter measure and an s-finite fibre measure, `memLp_two_of_uniform_slice` gives joint square integrability for a jointly almost-everywhere strongly measurable family whose fibres are almost everywhere in L² with uniformly bounded squared norms. The product integrability criterion applies to the squared norm because the integral in the fibre variable is bounded by an integrable constant. In `memLp_two_compact_weighted_sum` the parameter measure is Lebesgue measure restricted to a compact set. The component families are jointly almost-everywhere strongly measurable for the restricted product and have L² fibres with uniformly bounded squared norms on the compact set. Continuous coefficients are bounded there, giving square integrability of the finite weighted sum.

`CompactSpectralPacketPairingStatement` assumes locally finite noncentral measures `α` and `β`, a common s-finite fibre measure `μ`, and linear charts `A` and `A'` that carry `α.prod volume` and `β.prod volume` to unscaled Lebesgue measure on their respective full spectral spaces. The two families `f` and `g` vanish pointwise off compact spectral sets `C` and `C'` and are jointly in L² for the products of the restricted spectral Lebesgue measures with `μ`. Both positive-phase Fourier packets are in L² for `volume.prod μ`. Their pairing equals

$$
(2\pi)^m\int_{\mathbb R^m}\int\int
    \left(\int f(A(a,z),q)\,\overline{g(A'(b,z),q)}\,d\mu(q)\right)
    \,d\beta(b)\,d\alpha(a)\,dz .
$$

Here \(m\) is the central dimension and both the central frequency and the Fourier variable use unscaled Lebesgue measure. The function of \((z,a,b)\) in parentheses is integrable for `volume.prod (α.prod β)`.

The support indicator on each spectral space times the whole fibre leaves the integrand unchanged. This extends restricted square integrability to the full product. The proof transports along each measure-preserving chart and restricts the noncentral measure to the compact projection of the support. The central frequency is also supported in its compact projection. Almost every spectral slice is square integrable and hence integrable by compact support, so change of variables and Fubini give the coordinate packet formula with its unit-modulus phase.

The proof applies `coordinateWavePacketPairing` with the two restricted noncentral measures. The three-parameter integrand vanishes off the compact noncentral projections, which gives integrability and the iterated integral for the unrestricted measures. This supplies the compact-support step of the split-centre Plancherel argument in Lapid 2011, §8, printed p.328 (volume PDF p.337), `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
