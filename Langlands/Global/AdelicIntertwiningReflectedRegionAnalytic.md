# Agreement from integrability on the reflected regular region

`IntertwiningReflectedRegionIntegrabilityStatement` gives a uniform
threshold for absolute convergence of the actual rational-quotient
intertwining integral when `-weylParameter l c π' λ` is regular for the
target parabolic. This is one consequence of the inversion-root
convergence region described in Mœglin–Waldspurger, II.1.6(iv).

`intertwiningReflectedRegionAgreement_of_integrability` deduces
`IntertwiningReflectedRegionAgreementStatement` from that pointwise
integrability. In complex coordinates, each integrand is a constant
times the exponential of a complex-linear functional. Its norm is real
convex. The absolute convergence domain for each adelic argument is
therefore convex, and its interior contains both open regular regions.
The simplex majorant and dominated differentiation give holomorphy of
the integral there. The target height factor is entire.

The expansion is meromorphic on the intersection of the coefficient
domains, which is the whole parameter space for an empty expansion.
The integral and expansion agree on a nonempty open set of sufficiently
regular source parameters. The local-denominator identity theorem applies
on the interior of the absolute convergence domain, and gives equality
at each reflected regular parameter in the required domain.

Mœglin and Waldspurger, *Spectral decomposition and Eisenstein series*,
registered as `moeglin-waldspurger-1995-spectral-decomposition`,
`06.1_pp_78_100_Definitions.pdf`, SHA-256
`948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`,
II.1.6(i), (iv), pp. 87–90. The normalized integral is the one in
Bernstein and Lapid, *On the meromorphic continuation of Eisenstein
series*, registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
journal PDF SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`,
§2.2, p. 191.
