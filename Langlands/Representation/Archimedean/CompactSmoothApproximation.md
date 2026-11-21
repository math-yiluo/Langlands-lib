# Compact approximation in the genuine word-derivative topology

This internal development uses the jointly smooth orbit families and actual
compact integrals of `CompactSmoothAverage`. It works with genuine iterated
Lie derivatives on complex Banach representations of finite-dimensional real
Lie groups. The compact parameter space has its Borel measurable structure
and a finite measure that gives positive mass to every nonempty open set.

For a neighborhood of a family vector in `DerivativeSmoothVectors`, finitely
many genuine derivative coordinates suffice. Their continuity supplies a
neighborhood of the parameter. Every continuous compact weight whose complex
integral and integral of its norm are both one gives an average in the original
neighborhood, provided every parameter with nonzero weight belongs to the
chosen parameter neighborhood. This neighborhood estimate does not need the
Hausdorff or open-set positivity assumptions on the compact space. It
integrates the norm of the
weighted difference in each coordinate. Zero weights contribute zero even
when the parameter lies outside the neighborhood.

For the approximation conclusion the compact parameter space is Hausdorff.
Urysohn's lemma gives a continuous real bump that is one at the chosen
parameter point, nonnegative everywhere and supported in a prescribed
neighborhood. Its integral is positive because the measure is positive on
nonempty open sets. Dividing the bump by this integral, and regarding it as
a complex weight, gives both normalizations used above.

Thus a family vector at any point of the compact parameter image is in the
derivative-topology closure of all actual compact averages of that family.
Continuity of the averaging map in the uniform norm of the scalar weight,
proved in `CompactSmoothAverage`, places every average in the closure of
the averages with weights in any uniformly dense subset of `C(X, ℂ)`.
Taking closures gives the same approximation for the original family
vector. A submodule containing all these dense-weight averages therefore
contains that vector in its derivative-topology closure.

The orbit-family specialization uses translates of one genuine smooth vector.
If the compact parameter map passes through the group identity, these
dense-weight averages approximate the original vector itself.

`CompactSmoothApproximationStatement` asserts the family approximation
conclusion for every uniformly dense set of scalar weights.
`compactSmoothApproximation` proves it without additional representation
or density assumptions. All six type universes remain independent and free.

The argument adapts the published finite-coordinate neighborhood proof in
`Langlands.Global.ArchimedeanCompactIndexApproximation` to Banach-valued smooth
vectors and weakens the support requirement from the full parameter image to
the nonzero part of the weight. Its derivatives and averages are the original
ones, rather than a separate supplied seminorm family. This provides
approximation by actual averages, while compact-finite density still requires
a uniformly dense family of weights whose averages are compact-finite.
