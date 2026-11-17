# Assembling the actual archimedean inverse-transpose pairing

This internal construction for Task 7294 specializes the actual source-model
assembly to inverse transpose and connects all local identities to the
full archimedean action.

At each real or complex place, `compactTwist` is the actual inverse-transpose
map on the orthogonal or unitary matrix group, and `lieTwist` is negative
transpose complexified from the whole underlying real matrix Lie algebra.
The compact map agrees with `compactTranspose` under the actual place
inclusion: this is proved first in mixed matrix coordinates for the full
compact product and then for each individual factor. Likewise the real
Lie projections commute with negative transpose, giving the inclusion
identity on real directions and, by tensor induction, on their genuine
complexifications.

For an arbitrary complex representation of the full standard compact and
global complexified Lie algebra, a bilinear form satisfying all the
single-place transpose identities satisfies the global identities.
The compact proof uses the submonoid of elements preserving the form,
which contains all single-place factors. For the Lie identity, each
fixed pair of vectors defines a linear functional of the Lie direction;
the published place sum and complex scalar extension imply that a
functional vanishing on every place vanishes globally.

`PlaceDensityModels.transposeMultiplicityPairing` therefore constructs
a nonzero bilinear form on the actual finite-factor multiplicity space,
with the full compact and complexified Lie inverse-transpose identities,
from supplied nonzero transpose pairings on the chosen actual local
models. It uses the already proved density-model and finite-family
assembly constructions. The local form-existence hypotheses remain
explicit inputs. No local Gelfand--Kazhdan existence theorem, finite
adelic pairing, or unconditional global contragredient theorem is
asserted by this unit.

The provenance is internal: all comparisons are direct coordinate
proofs for the Library's actual local and global involutions, followed
by the implemented algebraic pairing assembly.
