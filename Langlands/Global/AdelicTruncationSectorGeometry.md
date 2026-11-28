# Regular truncation sectors and the generic pointwise estimate

`truncationSector` is the sector in the prescribed real norm chart
on the coroot space. Each simple root value is linear in the
truncation vector. This proves stability under positive dilation
and preservation of a nonnegative lower root cutoff under dilation
by at least one. The radial threshold \(R/\delta\) implies the
cutoff \(R\) within the sector. If there is a simple root, use the
operator norm of this root in the chart to choose a cutoff large
enough that every regular parameter has norm at least one.

`norm_le_of_tested_truncationIncrements` applies the convergence
theorem for regular starts to each fixed positive central translate.
For each compact subset of the generic spectral domain, the given
increment bound supplies the bound required by that convergence
theorem. For the final pointwise estimate, take the increment bound
on the whole intersection of the bounded spectral set with the
generic domain. This retains the same exponential rate and polynomial
dependence on the central translate, with its factor carried through
the geometric series. The resulting constant is strictly positive.
If the sector has no unit vector, scaling any nonzero vector to
unit length shows there can be no regular start of norm at least one.

The theorem takes the comparable-increment estimate and the vanishing
of smooth compactly supported tests as premises. These are the
automorphic and distributional inputs to the analytic step.
The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 25–26 and 31–32,
Theorem 7.1 and Lemmas 7.2 and 7.7.
