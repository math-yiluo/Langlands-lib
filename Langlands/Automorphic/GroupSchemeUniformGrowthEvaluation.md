# Evaluation in the uniform moderate growth topology

The continuous linear map `UniformGrowthFrechetSpace.evaluation` evaluates
a function of uniform moderate growth at a fixed actual adelic point.
The topology of `UniformGrowthFrechetSpace` makes every weighted derivative
continuous into the space of bounded functions with the supremum norm.
Take the derivative indexed by the unit of the enveloping algebra and
compose with the bounded-function evaluation. Multiplication by the
weight at the given point cancels the inverse weight in the derivative.
The weight is nonzero by positivity of the adelic norm for the given
matrix size. This gives the continuity of ordinary evaluation, whose
linearity follows from the operations on the function space.

The argument uses the weighted topology derived from Bernstein–Lapid
§7.1 in the Library. It supplies the evaluation maps needed to pass
from a continuation with values in that space to scalar meromorphy.
