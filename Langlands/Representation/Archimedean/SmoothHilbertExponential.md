# Differentiating the real exponential in the smooth-vector topology

`smoothHilbertExponentialSlope` is the smooth-vector difference quotient
of the actual curve \(t \mapsto R^\infty(\exp(tX))y\) at zero. Time is real
for either matrix field. `tendsto_smoothHilbertExponentialSlope` gives its
limit \(D_Xy\) in the topology induced by all genuine word derivatives.
`hasSmoothHilbertExponentialDerivatives` applies this convergence to each
continuous complex linear functional on that topology.

The proof identifies the tangent of the matrix exponential at zero in the
open units chart. It then inducts on a word \(W\) of matrix directions. The
orbit map of \(D_W R^\infty(\exp(tX))y\) is smooth jointly in \(t\) and the
group variable. Its derivative in \(t\) at zero is the orbit map of
\(D_W D_X y\). In the induction step the next Lie derivative is the partial
derivative along a second exponential curve. Smoothness of manifold
derivatives gives joint smoothness for the longer word, and symmetry of the
second Fréchet derivative in the two real parameters interchanges the
partials at zero. Evaluating at the group identity gives convergence in
each word coordinate. Continuous linear functionals preserve the resulting
limit and respect real scalar multiplication in the difference quotient.

This is an internal calculus lemma for the published genuine derivative
topology and `HasSmoothHilbertExponentialDerivatives` interface. It uses
smoothness of the given vector's orbit and boundedness of each acting
operator. It supplies the scalar exponential derivative clause of a
realization with that topology.
