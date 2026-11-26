# Smooth pullback with a fixed compactly supported weight

`CompactWeightedTestPullbackStatement` constructs a continuous complex-linear map between fixed-support smooth test spaces. For normed real vector spaces \(E,F\), a smooth map \(p:E\to F\), and a smooth weight \(w:E\to\mathbb C\) supported in the prescribed compact set \(K\), it sends \(f\) to \(x\mapsto w(x)f(p(x))\). The input test has support in a prescribed compact set \(L\) of \(F\), and the output test has support in \(K\).

The proof uses the compact-set bounds for each finite jet of \(p\) and \(w\). The iterated chain rule bounds the derivatives of \(f\circ p\) up to a fixed order by the maximum of the input seminorms to that order. The product rule gives the corresponding bound for \(w(f\circ p)\). This verifies continuity for the fixed-support seminorm topologies.

This estimate supplies the test-function continuity used when restricting a continuous Whittaker functional to the transverse test in the parabolic section of Jacquet, *Archimedean Rankin–Selberg Integrals*, proof of Proposition 14.1, pp. 103–104 of the author-posted edition. It is derived from the ordinary iterated chain and product rules.
