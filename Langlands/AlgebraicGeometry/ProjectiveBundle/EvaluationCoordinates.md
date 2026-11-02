# Evaluation in actual local frame coordinates

This derived unit connects genuine finite module-sheaf frames and their internal
duals to actual evaluation sections. Its inputs are module sheaves on a scheme
`S`, isomorphisms from the free sheaf with basis `ULift (Fin (n + 1))` on opens,
and a morphism of module sheaves. It proves the coordinate transformation law
from these inputs.

`LocalFrame.basisSection e W h i` is the inverse coordinate image of the standard
vector at `i`. `basisSection_eq` identifies it with the compatible local basis
section from `ModuleDualLocalFree`; `basisSection_restrict` proves restriction
compatibility.

`dual_basisCoordinate` identifies the coordinate functional of the dual frame
with evaluation on the corresponding primal basis section. The proof cancels
the dual frame isomorphism and uses `dualLocalFreeHom_evaluation`.
`dual_coordinates` expresses this identity on sections. `dual_basisSection`
identifies each dual basis section with the restriction of the primal coordinate
functional, using `dualLocalFreeIso_basis`.

Consequently, `dual_change_coefficient` identifies entry `(i,j)` of the change
from `e.dual` coordinates to `f.dual` coordinates with the `j`th `e` coordinate
of the `i`th `f` basis vector. `basisSection_change` gives the resulting expansion
of `f` basis vectors in `e` basis vectors. Its proof uses the inverse identity
for the genuine coordinate equivalence.

`LocalFrame.evaluatedSections e ev W h i` applies an actual module-sheaf morphism
`ev : M ⟶ N` to these basis sections. Naturality and linearity prove respectively
`evaluatedSections_restrict` and `evaluatedSections_change`. The latter states
that evaluated sections transform by the rows of the dual-frame coordinate
change, with no transformation-law hypothesis.

For `p : X ⟶ S` and `ev : M ⟶ p_* N`, `evaluationSections` regards these as actual
sections of `N` on `p ⁻¹ᵁ W`. `evaluationSections_change` specializes the row law:
each base coefficient acts through the genuine ring map `p.app W`. This follows
from the definition of scalar multiplication in module-sheaf pushforward.

The provenance is internal and derived from the published
`ProjectiveBundle.LocalFrame` and `ModuleDualLocalFree` constructions and
module-sheaf naturality. No external source assertion is introduced.
The unit does not assert generation, construct a global linear-system map,
or prove a cubic immersion or moduli representability.
