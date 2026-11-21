# The symmetric component of a quaternionic skew-hermitian form

`Langlands.GroupScheme.KneserThree.QuatData.symmetricComponent` uses a quaternion basis `1, x, j, jx`, with `x` generating the embedded quadratic field. It makes the second coordinate of a skew-hermitian form into a symmetric bilinear form over that field by applying the field conjugation. The scalar action on the original module is restricted along the quadratic field embedding.

The coordinate formulas for multiplication by field elements prove bilinearity. The second coordinate of a quaternion conjugate changes sign, so skew symmetry of the original form gives symmetry of the component. If the component pairs a vector trivially with every vector, multiplying any nonzero original pairing value on the right to obtain `j` gives a contradiction. Thus a nondegenerate skew-hermitian pairing has a nondegenerate component. Its self-pairing vanishes exactly where the original value lies in the ground-field line of `x`.

`exists_quatData_of_pure` prescribes an arbitrary nonzero pure quaternion as `x` in the existing quaternion basis construction. These comparisons implement the component `H` in T. A. Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups*, §1 and Proposition 5.3.2, printed pp. 106 and 109 (PDF pp. 112 and 115).
