# Compactness of projective points from bounded affine charts

Author: Worker 105.

This proof targets `NormedProjectivePointCompactnessProperty K`, with K an
arbitrary-universe nontrivially normed field whose norm topology is locally
compact. The carrier and topology are exactly the actual relative projective
points and `schemePointTopology` of the target statement. All natural dimensions,
including zero, and both characteristics are retained.

The implemented proof uses bounded affine charts. For each of the n+1 actual
homogeneous localization chart rings, the published ratios generate it as a
K-algebra. The existing finite-coordinate theorem therefore embeds its actual
algebra-point space as a closed subset of K^(n+1). Mathlib makes K a proper
metric space from the stated hypotheses, so each closed unit ball is compact.
The bounded chart is precisely the inverse image of their finite product
under the closed embedding, hence compact. Its image under the continuous
actual relative chart map is compact in `schemePointTopology`.

The existing bounded-chart construction proves that these finitely many
images cover all actual projective points: it re-evaluates the normalized
homogeneous vector at a coordinate of maximal norm. A finite union of the
compact images is thus the whole carrier, proving the exact target.

The motivation is the projective case of the local-field argument in Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Proposition 4.4, printed page 11. This proof uses a chosen nontrivial norm and
does not supply full topological-field properness, a compatible norm,
nonprojective proper-scheme compactness, or adelic compactness.
