# Simultaneous compact families of equal-rank data

`Langlands.RankinSelberg.equalRankCompactData` proves
`EqualRankCompactDataStatement F n`, preserving its independent field and
representation universes, both character signs, and arbitrary specified
functionals, including zero functionals.

The implemented proof applies `Whittaker.model_isSmooth` to each coefficient
image. Then `Hecke.orbitMap_locallyConstant` makes each of the two model-vector
orbit maps locally constant. The third component is locally constant by
`HarmonicAnalysis.rowTranslate_locallyConstant`, which follows from the open
stabilizer of the Schwartz–Bruhat row test.

Taking the product of these three maps yields exactly the simultaneous tuple
in the statement. For any compact subset of the general linear group, its
subspace is a compact space. Restricting the tuple along the continuous
subtype inclusion preserves local constancy. The finite-range theorem for
locally constant maps on compact spaces proves the remaining assertion.
No topology on either coefficient-image carrier or on the row-function
codomain is used.

This is the elementary topological argument for the derived target motivated
by the compact-group finiteness step in the proof of Theorem 2.7 of
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983),
printed p. 391, paragraph before display (3). It supplies simultaneous finite
data, without asserting a measure decomposition or any analytic conclusion.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391.
