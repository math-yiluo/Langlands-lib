# Dense source subspaces for smooth projective products

`SmoothProjectiveProductSourcesStatement` concerns a finite family of jointly continuous representations on complex Banach spaces, with acting groups the units of finite-dimensional real Banach algebras. A source with dense image in the genuine smooth carrier of each factor yields a dense span of pure tensors in the genuine smooth carrier of the product group acting on the completed projective tensor product.

`continuous_pureSmooth` uses the topology of all word derivatives. The empty word is the continuous pure tensor map on the original Banach spaces. For a further derivative, split its direction into the finitely many coordinate axes. On a pure smooth tensor each axis derivative acts on the corresponding coordinate. Induction on the word gives continuity of every coordinate of the pure tensor map. The product of the given dense images is dense. Continuity places every pure smooth tensor in the closure of the source span, and `smoothProjectiveProductDensity` then places the whole smooth carrier in that closure.

This is a derivative-topology density result for the passage from pure tests to joint smooth vectors used in [Jacquet, *Archimedean Rankin–Selberg Integrals*, §12.3, pp. 89–90](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=89).
