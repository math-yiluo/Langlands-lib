# Adjacent-rank induction with exponential strip growth

`complexAdjacentFromEqualGrowthAtCharacter` takes the normalized equal-rank equation with exponential strip growth at a nonzero trace-character parameter `a` and proves the corresponding adjacent-rank equation. Both statements quantify over the exact induced Whittaker models and all inducing character lists of the indicated lengths. `complexAdjacentFromEqualGrowth` specializes the implication to the standard character.

The proof identifies each model with the range of the canonical Jacquet map. It uses canonical parameter `-a` for the larger vector, which has left character parameter `a`. The lower equal-rank equations are evaluated on the partial row Fourier test. The absolute convergence input comes from `complexLocalEqualPairConvergence`. Row Fourier inversion gives the dual test. The canonical adjacent theorem with strip growth then proves the equation for the original pair of functions.

This is the adjacent step used in the induction with exponential strip growth. [Jacquet, *Archimedean Rankin–Selberg integrals*, Sections 8–9](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
