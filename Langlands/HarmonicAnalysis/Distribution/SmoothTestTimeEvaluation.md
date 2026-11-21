# Differentiating evaluations of smooth test families

`eval_compactTestTimeDerivative_of_hasDerivAt` identifies the derivative
of the response of a continuous linear map to a jointly smooth family
of tests with a common compact support. The result applies whenever
that response is represented on an open interval by a differentiable
function of the parameter.

The smooth divided difference has the same support. At nonzero time
this follows from the difference identity. At zero it follows by
differentiating the slices that vanish outside the compact set. The
divided differences therefore vary continuously in the fixed-support
test topology. Off zero their evaluations are the response's slopes,
so uniqueness of the scalar limit gives the claimed evaluation at zero.
This internal result supplies differentiation of translation covariance.
