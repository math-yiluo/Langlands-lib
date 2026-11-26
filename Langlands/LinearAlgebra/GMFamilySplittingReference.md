# Reference intercepts for two chambers

`pairedNormals` presents the two chambers' simple roots with labels in a sum
type. `sum_normalizedWeight_eq_zero_of_ne` evaluates the generic-intercept
sum for distinct chambers. A root positive on the first chamber has its
negative positive on the second. A feasible basis with every intercept
positive would give positive evaluation on both of these roots, because
positive roots are positive combinations of the simple normals. This is
impossible, so the sum is zero by generic-intercept invariance.

`sum_normalizedWeight_eq_left` treats two copies of the same chamber. The
reference inequalities have a larger intercept on every left normal than
on its duplicate to the right. The left copy is the unique feasible basis.
The reference arrays used in the proof are chosen regular while preserving
these respective conditions.
