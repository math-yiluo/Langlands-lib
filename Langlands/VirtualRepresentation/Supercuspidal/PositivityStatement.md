# Norm-one extraction on the genuine supercuspidal lattice

Worker 30 states the target-side extraction step using the actual
`PadicSupercuspidal.UnitaryBasis F` and its free integral lattice.
The field is any actual `PadicField p`, with prime `p` and the constructed
canonical topology. Field and representation-carrier universes are
independent. A basis element is a genuine supercuspidal isomorphism class
with its positive general linear group rank, together with the descended
existence of an invariant positive Hermitian form. It is not a class of an
arbitrary irreducible admissible representation.

`UnitarySignedBasisStatement` asserts that a virtual vector of integral
self-pairing one determines a unique such basis class, with the vector equal
to either its multiplicity-one generator or the negative of that generator.
The disjunction retains the sign ambiguity. The quantified vector has actual
finitely supported integer coefficients and the pairing is their dot product.

`UnitaryPositiveBasisStatement` separately assumes strictly positive degree
and concludes that the vector is the positive generator of a unique basis
class. This degree is the integer-linear extension of positive group rank.
It is not a dimension of the smooth representation carrier. The latter has
no finite-dimensionality or carrier-topology requirement.
`UnitaryNormOneExtractionStatement` is the conjunction of these two
propositions. All three are `Prop` definitions, not proofs.

The original application is Henniart, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique* (2000), Section 2.5,
printed pages 445--446, and the corollary and following argument in
Section 2.6, page 447. The free groups have orthonormal class bases;
the global generators have unitary supercuspidal support. Restricting to
that unitary subbasis retains the coefficient pairing and positive rank
weights. The passage from a signed basis image to a positive image uses
preservation of positive degree. Section 2.7, page 447, keeps the
subsequent spanning and choice-independence steps separate. Literature ID
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
These original sections were read. This statement isolates the elementary
extraction consequence from its use in the correspondence construction.

The two propositions specialize the integer-coefficient argument already
expressed in `Langlands.VirtualRepresentation.DescentStatement` to the
genuine automorphic target. A sum of integer squares equal to one has one
coefficient equal to one or minus one and all other coefficients zero;
positive group-rank weights exclude the negative case when degree is
positive. This explains the derived provenance and does not assume a proof
of the generic statement or the existence of any correspondence.

The direct import is Worker 24's published
`Langlands.VirtualRepresentation.Supercuspidal.Basic`, with Lean SHA256
`27a08f4c78ca7c2310d0e6e1722fd8093886787f818e1be5a5aab641fa3411a8`
and Markdown SHA256
`86d0ae121e859810cfefdb891ec845e20ebcf1e8afd3777c6786b952846726e8`.
The complete pair and independent review were read, and the published
bytes were verified in Library commit
`68e8013fc4fed0de284fd849695676aca2e0c32d`.
Its actual class prerequisite, Worker 23's
`Langlands.Representation.Classification.Supercuspidal`, is also published.
Both complete construction pairs were read. Their intrinsic quotient and
support laws supply the objects; neither theorem conclusion is a field.
A fresh Lean-service check against the published Basic pair succeeded
without diagnostics and confirmed the closing declaration returns `Prop`
with only standard assumptions. The complete proposition bodies were already
inspected in the original development. Imported implementations retain
their original authorship and are not part of this submission.

Relation independence, construction of an integral map from the local Weil
side, its pairing and degree identities, signed basis injectivity, removal
of auxiliary choices and final numerical surjectivity are separate theorem
obligations. They are not supplied by this target-side extraction statement.
