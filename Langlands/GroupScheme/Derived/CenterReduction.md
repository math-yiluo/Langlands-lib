# Full-centre comparison under a central product

This internal reduction for derived-subgroup semisimplicity concerns full
subgroup functors on all test schemes. Suppose the ambient group scheme over
an arbitrary field is affine, the second factor is a closed subgroup, the
first factor is central, and the actual product morphism is an epimorphism.
Then the centre of the second factor is the inverse image of the ambient
scheme-theoretic centre.

The proof first uses the published closed representability of centralizers
of closed subgroups over a field. Let `C` represent the centralizer of the
second factor. Symmetry of centralization places the second factor in the
centralizer of `C`, and centrality places the first factor there. The latter
centralizer is itself closed and represented. The product detection lemma
therefore makes it the whole group. The double-centralizer inclusion now
places `C` in the full ambient centre. The reverse inclusion follows directly
from the definition of centrality.

A central point of the second factor commutes with its points after every
refinement, so its image lies in `C`, hence in the ambient centre. The reverse
inclusion follows by cancelling the monomorphic subgroup inclusion. This
proves equality of the two subgroup functors.

Given a closed representative `c : C ⟶ D` of that ambient-centre preimage,
`isSchemeTheoreticCenter_of_center_preimage_of_epi_subgroupProductMap`
identifies `c` as a full scheme-theoretic centre representative.
`centerPreimagePointsEquiv` then constructs the multiplicative equivalence
between points of `C` and full centre points of `D` on every test scheme,
using the existing represented-subgroup `pointsEquiv`. Its underlying point
map is composition with `c`, as `centerPreimagePointsEquiv_apply_coe` states.

Finally, an actual finite closed representative of the ambient-centre
preimage represents the centre of the second factor by this equality. This
establishes `HasFiniteCenter` without choosing any additional centre
representative. The existence and finiteness of that preimage remain explicit
hypotheses; the file does not prove the finite central-intersection theorem
for reductive groups or any of the connected-reductivity obligations.

This is an internal construction and elementary reduction for the
derived-subgroup semisimplicity proof. Its inputs are the existing full
centre, subgroup-functor and represented-subgroup interfaces, closed
centralizer representability over fields, and the epimorphic-product
detection lemma; it introduces no external structural assertion.
