# Schwartz functions under the operator and entrywise matrix norms

`operatorToEntry` takes a complex-valued Schwartz function on a finite complex matrix space with supremum row-sum norm and gives a Schwartz function on the same matrix space with supremum entry norm. Its value on every matrix is the original value.

Both norms induce the product topology on the matrix coordinates. The Lean construction uses the identity continuous real-linear equivalence with the norm structures supplied explicitly to `SchwartzMap.compCLMOfContinuousLinearEquiv`. The pointwise equality follows by definition of that pullback.

This is internal infrastructure for applying the entrywise-norm Godement partial Fourier transform to compact cofactor tests constructed with the operator norm.
