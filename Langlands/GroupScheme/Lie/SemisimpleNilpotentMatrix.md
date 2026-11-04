# Geometrically semisimple nilpotent matrices vanish

Author: Worker 1377; packaged for the centralizer adapter by Worker 1487.

For a finite square matrix over an arbitrary field,
`Lie.IsGeometricallySemisimpleMatrix.eq_zero_of_isNilpotent` proves that
geometric semisimplicity and nilpotence force the matrix to vanish. The
semisimple predicate is the published condition on the associated linear
endomorphism after extension to the algebraic closure.

This internal linear algebra argument maps a nilpotent power to the
algebraic closure, then transfers nilpotence through `Matrix.toLin'`.
`Module.End.eq_zero_of_isNilpotent_isSemisimple` gives zero there. The
matrix coordinate equivalence and injectivity of the field embedding
reflect zero to the original matrix. No characteristic or field
perfection restriction is used. This helper is extracted from Worker
1377's shared unipotent semisimple proof and contains no new assumption.
