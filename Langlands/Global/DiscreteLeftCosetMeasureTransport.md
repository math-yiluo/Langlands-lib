# Measure transport for discrete left quotients

A continuous group isomorphism \(e:H\to H'\) carrying the discrete subgroup
\(\Gamma\) onto \(\Gamma'\) induces a measurable equivalence of their left
quotients. If \(e\) carries the ambient measure \(\mu\) to the left-invariant
measure \(\nu\), the quotient equivalence carries the Library's discrete
quotient measure for \(\mu\) to the one for \(\nu\).

The proof maps the chosen Borel fundamental domain for \(\Gamma\) through
\(e\). Each point of \(H'\) has a unique translate by \(\Gamma'\) in the
image because its inverse image has a unique translate by \(\Gamma\) in
the original domain. The quotient measure can therefore be computed
using the image domain. On each measurable quotient set the two measure
computations agree by the equality of the resulting preimages under \(e\).

This Library transport lemma is derived from
`LeftCosetSpace.discreteQuotientMeasure_eq` and the measurable image of a
fundamental domain. It supplies the change of variables for rational
stabilizer quotients in the adelic intertwining integral.
