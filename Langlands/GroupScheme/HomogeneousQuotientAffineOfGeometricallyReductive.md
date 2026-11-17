# Affineness of a supplied quotient under geometric reductivity

Worker 525. This internal derived construction completes the conditional
affineness argument for the actual supplied homogeneous quotient. Geometric
reductivity remains an explicit hypothesis. The module does not prove the
unconditional `ReductiveLinearQuotientAffineStatement`.

Let k be a field, H and J group schemes over Spec k, i a homomorphism H to J,
and Q a supplied `HomogeneousQuotient i`. The structure
`AffinePrincipalUnitCertificate` consists of a natural number n and sections
t indexed by Fin n, with each principal open Q[t_j] affine and
Ideal.span(range t) equal to the unit ideal in the actual ring of global
sections of Q. The structure itself imposes no algebraic closedness,
smoothness, affineness of H or J, or reductivity assumption.

The remaining declarations assume k is algebraically closed, H is smooth and
affine, J is affine, and the explicit predicate `IsGeometricallyReductive H`
holds. The family size is unrestricted. All hypotheses and conclusions use
the original supplied Q, and its exact all-test coset-fiber and projection
data. No restriction is placed on the characteristic or on relative scheme
tests, including nonreduced and nonaffine tests.

`span_eq_top_of_ambient_certificate` starts with a finite family t of quotient
sections and ambient coefficients a such that sum_j a_j*p*(t_j)=1.
The invariant-section ring equivalence sends t_j to the right-invariant
ambient section p*(t_j). The invariant unit-ideal theorem reflects the
ambient relation into the invariant subring. Transporting its ideal equality
back through the bijective ring equivalence proves Ideal.span(range t)=top
in the quotient section ring itself. The proof uses commutativity to put
the ambient relation in the orientation required by the unit-ideal theorem.

`affinePrincipalUnitCertificate` obtains a finite family of quotient sections
with affine principal opens and an ambient coefficient relation from the
principal-neighborhood construction. It applies the preceding reflection
lemma to construct an `AffinePrincipalUnitCertificate` on Q.

`isAffine_of_geometricallyReductive` applies Mathlib's affine basic-open
criterion to this certificate. Its two inputs are the unit ideal generated
by these actual quotient sections and affineness of every corresponding
principal open. Thus the conclusion is `IsAffine Q.scheme.left` for the
same quotient supplied to the construction.

The provenance is internal: finite ambient certificates, the polynomial
invariant unit-ideal argument, effective descent of invariant sections and
Mathlib's affine basic-open criterion imply the result. This is not a
transcription from original literature. An independently proved
geometric-reductivity theorem and the exact reductive linear-quotient target
adapter remain separate obligations.
