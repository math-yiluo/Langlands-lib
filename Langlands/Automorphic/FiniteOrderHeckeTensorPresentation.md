# Actual restricted tensor presentations of finite-order automorphic Hecke lines

This internal construction supplies actual finite tensor presentations for the
previously constructed automorphic determinant-character lines. The number
field has arbitrary universe, the matrix rank is any natural number, and the
coefficient field is the complex numbers. A finite-order Hecke character is
supplied. No factorization existence hypothesis is supplied.

The local factors are the existing scalar representations of the actual local
determinant characters. Every reference vector is one. The exceptional set is
the previously constructed `finiteDeterminantTail`: finite order proves
triviality on the whole integral reference tail, including elements with
infinitely many nonidentity integral coordinates. Its local consequence proves
`tensorReference_fixed` outside this finite set.

`finiteTensorScalarEquiv` identifies the constructed restricted tensor of these
local character lines with the finite adelic determinant-character line. Its
underlying linear map is multiplication of the finite tensor entries, descended
through the actual direct limit. For equivariance, the implementation pulls the
existing full-tail character tensor equivalence across the actual continuous
group equivalence between finite adelic matrices and their local restricted
product. The existing singleton-character comparison identifies its local
characters with the local determinant characters, and the finite determinant
comparison identifies its global character with the finite adelic determinant.
The elementary-tensor formula is the product of all entries, including the
empty product.

`finiteTensorPresentation` composes this equivalence with the existing faithful
scalar model of the actual finite form image of the whole operator realization.
Its reference vectors are nonzero. The associated form-valued tensor map is
injective and its range is exactly this prescribed actual line. On an elementary
restricted tensor with entries `x`, its represented function at a full adelic
matrix `a` is

`χ(det a) * ∏ v, x v`.

Thus the presentation concerns an actual embedded subspace of automorphic
functions, retaining the original finite action and full adelic evaluations.

For each finite place, `tensorTailVector` constructs a specific complementary
tensor as the inverse scalar image of one. The scalar equivalence proves that
it is nonzero, including if the complementary index type is empty. The existing
tensor-slice equivalence identifies the resulting actual local slice with the
local scalar character model. Composing with the previously constructed whole
local form equivalence proves equality of their local representation classes.
Outside the exceptional set the published integral-fixed-vector construction
gives a nonzero vector in this actual slice fixed by the actual local integral
subgroup.

The provenance is internal: this pair combines the existing full-tail
determinant construction, actual restricted tensor equivalence for scalar
characters, local and finite scalar models of the actual automorphic line, and
the published faithful tensor-image and slice constructions. No new
original-literature identification, general automorphic factorization,
topological tensor completion, Satake computation or ramified local-global
compatibility is asserted. All representation equivalences here are algebraic;
the finite and local group topologies are the previously established actual
adelic and completion topologies.
