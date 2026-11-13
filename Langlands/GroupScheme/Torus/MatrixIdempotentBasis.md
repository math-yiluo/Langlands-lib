# A basis from a complete family of orthogonal matrix idempotents

Let L be an arbitrary field, n a finite index type, and e a family of square
matrices indexed by any label type M. The definition `columnFamily` indexes
all columns of all members of the family by M times n.

If some finite sum of the matrices is the identity, their columns span L^n:
for each standard basis vector, take that column of the sum. A vector-space
basis can therefore be selected from this column family, reindexed by n.
This first construction does not require idempotence or orthogonality.

Assume next that e(m)e(p) is e(m) for equal labels and zero for distinct labels.
Each projector acts on the selected basis columns by the corresponding
Kronecker rule. If a nonzero projector's label did not occur in the selected
basis, its linear map would annihilate every basis vector and thus be zero.
Injectivity of the matrix-to-action map contradicts its nonzero assumption.
The final existence theorem supplies a column basis together with this label
coverage property.

This is internal auxiliary linear algebra for the Hermitian split-rank upper
comparison. It follows from the published Mathlib basis-selection and matrix
linear-map APIs. No infinite-field, characteristic, Hermitian-form or group
scheme hypothesis is used. It does not itself prove an isotropy assertion.
