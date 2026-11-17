# Compact factors in padded simple-root gauges

This internal helper applies the published `StandardCompactPadding` matrix
identities to the standard compact subgroup in the simple-root gauge predicate.
`pad_mem_gaugeStandardCompact` transports their full adelic assertion to
actual group-scheme points.

`exists_gaugeIwasawa` refines the Library's upper-triangular-times-compact
factorization to a unipotent-times-diagonal-times-compact factorization.
The diagonal entries of the upper triangular matrix are ideles, with inverses
read from the inverse matrix. Multiplication on the right by the inverse of
their diagonal matrix leaves an upper unitriangular matrix. The Library's
unitriangular membership criterion constructs the required unipotent point.

`IsAdelicSimpleRootGauge.exists_padded_formula` removes the padded compact and
unipotent factors using the two invariances in the gauge predicate. The padded
diagonal identity and the telescoping root-norm identity then identify the
remaining gauge value with its Schwartz function times the negative power of
the first diagonal norm. It uses the published gauge definitions.

The provenance is the Library's padding construction and matrix-unit algebra.
These results assert no convergence or Whittaker majorization.
