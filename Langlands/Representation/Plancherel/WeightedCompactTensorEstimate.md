# The norm estimate for a weighted tensor of ordered intertwiners

`weightedTensor_norm_tmul_le` is the linear algebra of the weighted compact
estimate. It composes the first factor with the outer return map. The
composition law and the round-trip scalar turn the result into a scalar
multiple of the inverse first factor of the normalized comparison. The
bound for the outer return map and preservation of the product of compact
norms then give the estimate in the tensor norm. The bound retains the
composition constant and the scalar from the weighted round trip.

`exists_uniform_tensor_bound_of_tmul` extends the pointwise estimate by
algebraic tensor induction and the triangle inequality. These steps implement
the norm estimate used in Waldspurger V.2.2 and V.2.3, printed pp. 293–294.
