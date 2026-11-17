# Unit ideals in actual right-invariant section rings

Worker 525. This derived supporting unit constructs the polynomial of covariant
rows over the actual invariant section ring and proves a unit-ideal reflection
theorem for the invariant subring of global functions on an affine group. It
uses Worker 690's covariant-family and normalized homogeneous-separator
interfaces. Geometric reductivity is an explicit hypothesis in the unit-ideal
theorem. No independent reductivity theorem or quotient affineness is claimed.

The two polynomial identities work for any commutative coefficient rings k,A
with a k-algebra structure on A. `linearFamilyPolynomial_eq_eval_map` expresses
the existing substitution polynomial using the scalar extension of its
original polynomial. `linearFamilyPolynomial_matrix` shows that applying a
matrix to each row of a finite coefficient family amounts to linear
substitution by that matrix in the scalar-extended original polynomial. Its
proof expands the two finite sums and exchanges their order. The row and
coordinate sets may be empty.

For the group-scheme results, k is a field, H and J are actual group schemes
over Spec k, and iH is a homomorphism from H to J. The invariant subring is
defined by equality after right translation on every relative scheme test,
including nonreduced and nonaffine tests.

`isRightInvariant_coeff_linearFamilyPolynomial` assumes H is affine. Suppose
all rows f_i are covariant for a common finite matrix representation rho of H,
and F over k is invariant under transpose substitution on every relative
test. Then every coefficient of linearFamilyPolynomial(f,F) is an actual
right-invariant section on J. No smoothness, algebraic closedness, affineness
of J or geometric reductivity is required for this coefficient lemma.

The proof first converts transpose invariance into invariance for rho.dual,
by testing at the inverse point. The published universal polynomial theorem
for an affine acting group turns this all-test assertion into equality of
polynomials over the section ring of any test. Testing the dual identity at
an inverse point yields the transpose coefficient identity for rho. Algebra
maps induced by the two ambient points carry the family polynomial to the
polynomials of their pulled-back rows. Covariance and the matrix-substitution
identity make these equal. Equality of each coefficient is precisely the
required all-test invariance. This argument uses a universal polynomial
identity and does not infer coefficient equality from rational-point density
in a possibly nonreduced ring.

`rightInvariantFamilyPolynomial` takes the same affine H, homomorphism iH,
finite representation, covariant rows, and transpose-invariant polynomial F.
It returns a polynomial in the row variables with coefficients in
`rightInvariantSubring iH`. The construction uses classical choice on the
coefficient-lifting theorem, justified by the preceding all-test invariance
lemma. `map_rightInvariantFamilyPolynomial` proves that applying the subring
inclusion to its coefficients recovers exactly `linearFamilyPolynomial(f,F)`.
This construction requires no geometric reductivity, smoothness, algebraic
closedness or affineness of J.

`span_eq_top_rightInvariantSubring` assumes k is algebraically closed, H is
smooth and affine, J is affine, and H is geometrically reductive. Given a
finite family s_i in the actual right-invariant subring and arbitrary ambient
coefficients a_i with sum_i s_i*a_i = 1, it proves that the s_i generate the
unit ideal in that invariant subring itself.

The scalar covariant coefficient construction supplies rows g_i and a nonzero
dual-fixed scalar vector c with sum_i s_i*g_i,j = c_j. Geometric reductivity
supplies a positive-degree homogeneous transpose-invariant polynomial F
normalized by F(c)=1. For P(T)=F(sum_i T_i*g_i,j), the preceding lemma puts
every coefficient of P in the invariant subring. Positive homogeneity makes
its constant term zero. Substituting s_i for T_i evaluates P to one because
the weighted columns are c. The generic polynomial certificate theorem then
proves the unit ideal in the invariant subring. No division by the homogeneous
degree is used, so the argument retains arbitrary field characteristic.

The provenance is internal: finite polynomial substitution, the published
universal invariance interface, scalar covariant coefficients and normalized
homogeneous separation imply the result. It is not a transcription from an
original source. The independent geometric-reductivity prerequisite and the
application to the same supplied homogeneous quotient remain separate.
