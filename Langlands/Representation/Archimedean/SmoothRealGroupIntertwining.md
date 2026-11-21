# Full group equivariance of continuous smooth intertwiners

`Langlands.Archimedean.DerivativeSmoothVectors.SmoothRealGroupIntertwiningStatement`
concerns two jointly continuous representations of `GLₙ(ℝ)` on complex normed
spaces. A continuous linear map between their genuine smooth-vector carriers
which commutes with each real Lie derivative and the orthogonal action
intertwines the full group action.

For a differentiable group path from the identity, the proof conjugates the
image of the source orbit by the inverse path in the target action. The
derived intertwining identity and conjugation of Lie directions cancel the two
terms in its derivative. Each normed word coordinate is then constant by the
mean value theorem, and the coordinates separate smooth vectors. Iwasawa
decomposition expresses an arbitrary real invertible matrix as an exponential
of a real diagonal matrix times an upper unipotent and an orthogonal matrix.
Scaling the diagonal exponent and the strictly upper entries gives the required
path for the first two factors. The compact identity handles the last factor.

This internal result uses the Library's genuine word-topology differentiation
of unit actions. It upgrades continuous extensions of compact-finite block
maps to full group intertwiners.
