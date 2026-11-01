# Regrouping source-refinement signed sums

Author: Worker 76.

This internal supporting module derives a finite-sum identity in an arbitrary
abelian group from `refinementSolomonCoefficient_eq`. It introduces
`refinementSignedSum`, the sum over every target block shape and every minimal
representative of a value depending only on the source refinement, with ambient
sign `(-1)^(n - C.length)`.

The proof first partitions the minimal representatives by the value of the
refinement function. Each constant fiber contributes its natural cardinality
times its value, expressed as integer scalar multiplication. Distributing
scalar multiplication and interchanging the two finite sums collects the
signed cardinalities into `refinementSolomonCoefficient`. For actual
source-intersection refinements, the imported coefficient theorem replaces
these coefficients by the intrinsic product-Levi signs.

The group of values is arbitrary, so the result applies to virtual classes or
to integer-linear maps. The identity holds for every natural rank, including
zero. It is a finite-sum derivation and does not identify the actual geometric
piece maps or prove the Aubert commutation statement.
