# Packaging a Levi embedding as supercuspidal support

Author: Worker 195. These are internal transport and packaging helpers used
by [SupercuspidalEmbeddingProof](SupercuspidalEmbeddingProof.md).

`exists_cuspidalSubrepresentation_of_product_embedding` takes actual
supercuspidal factors of an ordered block shape and an injective intertwiner
from an irreducible smooth representation into their normalized product. It
forms cuspidal data from the ranks and isomorphism classes of those factors.
The reconstructed block shape is definitionally the given shape. The factors
represent their classes by reflexivity, and the original intertwiner witnesses
the published `IsCuspidalSubrepresentation` relation.

`exists_cuspidalSubrepresentation_of_levi_equiv` takes a Levi representation,
an actual equivalence to the external tensor of supercuspidal factors, and an
injective intertwiner from the given irreducible smooth representation into
normalized induction of that Levi representation. It induces the equivalence
using `normalizedParabolicInducedEquiv`, composes with the given embedding,
and applies the first helper. The factor universe, the Levi carrier universe,
and the field universe remain independent.

Both helpers are elementary consequences of the published definitions and
the induction transport construction. They assume concrete maps and an actual
equivalence, and do not assert the deep existence of a cuspidal Levi embedding
or exhaustion of irreducible Levi representations by external tensors.
The closing proof supplies these inputs from the separately published
cuspidal embedding and Levi tensor factorization theorems.
