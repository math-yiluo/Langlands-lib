# Uniform small exponential charts for closed subalgebras

Over a nontrivially normed ultrametric field of characteristic zero, let `A` be a complete ultrametric normed algebra. `SmallExponentialSubalgebraStatement` gives a positive radius bound such that every smaller positive-radius closed ball at zero lies in the convergence domain of the exponential. For every closed subalgebra `S` of `A`, the map `x ↦ exp x − 1` is an isometric self-bijection of the intersection of this ball with `S`. The same bound works for all the subalgebras.

A closed algebra embedding commutes with the exponential by the formula as the sum of its power series and transport of series along a closed embedding. Thus the exponential preserves each closed subalgebra. The strict derivative of `exp − 1` at zero is the identity. On a small ball its difference from the identity is a strict contraction, so the ultrametric inequality gives an isometry. For `y` in the intersection of the ball with `S`, the map `x ↦ y − ((exp x − 1) − x)` preserves the intersection and is a contraction. Its fixed point maps to `y`.

This supplies the uniform local charts used when constructing an invariant exponential domain by changing basis in a fixed ambient algebra. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.4, p. 155](https://doi.org/10.4153/CJM-1987-008-3)
