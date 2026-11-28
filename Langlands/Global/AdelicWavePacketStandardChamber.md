# Nonempty open chambers of standard regular parameters

`StandardRegularRegionStatement` concerns the real-coroot inequalities
`IsStandardRegularParameter` for a standard parabolic. It uses a
retraction of the parabolic onto its Levi. At any real threshold, the
parameters satisfying the inequalities form a nonempty open set in
every complex linear chart.

`isOpen_standardRegularRegion` expresses the region as a finite
intersection of strict inequalities for continuous real linear
functionals. For nonemptiness, `exists_standardRegularParameter`
sums the full fundamental weights for the simple roots outside the
Levi. The sum evaluates to zero on the selected Levi coroots and to
one on the complementary simple coroots. The standard Levi
character-image theorem and the retraction realize it by restriction
from the parabolic. Multiplying by \(R+1\) and taking the real
complexification gives a parameter at threshold \(R\).
`standardRegularRegion` transports this witness to the given chart.

The inequalities describe the sufficiently regular positive chamber
used for the convergent Eisenstein series and intertwining operators
in E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §2, pp. 311–312
(volume PDF pp. 320–321). The open nonempty coordinate region is used
for meromorphic uniqueness.
