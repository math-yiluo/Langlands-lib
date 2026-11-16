# Actual type-A opposition is chain reversal

For any actual Tits index over any field, a numbering preserving the full type-A
Cartan matrix identifies opposition with chain reversal, provided the integral
coroots span the full cocharacter lattice. Simple connectedness of the group
supplies this span, so the conclusion holds for every simply connected group
with such a numbering, in every characteristic and universe. No rank-one or
local-field hypothesis is required. `numberedOpposition` conjugates the actual
opposition permutation by any supplied numbering, and the final theorem
identifies this numbered permutation with `Fin.revPerm`.

This is an internal consequence of the published actual-opposition construction,
the classification of type-A Cartan symmetries as identity or reversal, and the
weight-residue obstruction in `TypeANegationWeyl`. For rank at least two, if
opposition fixed every vertex, the full-lattice based automorphism would be
identity: pairings with the spanning simple coroots detect every weight. The
kernel of the based projection is the integral Weyl subgroup, so this would put
full-lattice negation in that subgroup, contrary to the residue obstruction.
Thus the Cartan symmetry is reversal. The empty and one-vertex cases follow
from their sizes. Simple connectedness ascends to the separable closure; the
published necessity direction of the split coroot criterion then proves full
integral coroot span of the supplied actual root datum. This step reuses
`TitsIndexData.pinning_corootSpan_eq_top` from `TypeDVectorQuotient`, whose
statement is general and does not require a type-D hypothesis.

The result identifies the existing opposition permutation. The imported
opposition theorems give its preservation of the actual distinguished subset
and its commutation with every absolute Galois element. This unit does not yet
assert the central marked position or the full local rank-one enumeration.
