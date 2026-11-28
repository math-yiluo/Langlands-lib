# Rescaling a representative of an orbit of lattice cosets

Let `A` be a proper finite-dimensional ultrametric normed algebra over a complete nontrivially normed field `F`. For `d : F`, `nilpotentAnnulus d A` is the set of nilpotent elements with norm between `1/‖d‖` and `1`. The characteristic coefficients of left multiplication realize the nilpotent cone as a closed set, so this annulus is compact.

`NilpotentOrbitRescalingStatement` starts with an open neighborhood `V` of that annulus and supplies an open neighborhood `W` of the annulus. For each compact additive subgroup `L`, subgroup `K` whose conjugations are norm isometries, and bound `b > 0`, there is a threshold `t > 0`. For `‖x‖ > t` and `y = k x k⁻¹ + l` with `k ∈ K` and `l ∈ L`, one has `‖y‖ > b`. If some nonzero scalar `a` has `‖a • y‖ ≤ 1` and `a • y ∈ W`, the statement gives a nonzero scalar `a'` with `a' • x ∈ V`.

The proof takes `W` to be the open `ε`-thickening of the compact nilpotent annulus inside `V`. With `D` a common bound for the norm on `L`, take `t = max(b, D, D/ε)`. The ultrametric inequality gives `‖y‖ = ‖x‖`, and `‖a‖ D < ε` follows from `‖a • y‖ ≤ 1`. Conjugating by `k⁻¹` preserves the thickening and puts `a • y` within `ε` of `a • x`. A second ultrametric inequality places `a • x` within `ε` of the annulus, so the proof chooses `a' = a`.

This estimate gives the transfer from a frequency in an orbit of lattice cosets to the frequency specifying the Fourier test in the proof of Lemma 12. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.7, pp. 162–165](https://doi.org/10.4153/CJM-1987-008-3)
