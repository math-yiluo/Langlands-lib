# Two module sheaves glued from one overlap isomorphism

This is a derived construction using the Library's module-sheaf pushforward,
restriction adjunction, and canonical comparison with actual module pullback.
It applies the compatible-pair construction underlying
`OpenCoverModuleGluingProof` to two open immersions and one prescribed overlap
isomorphism, reusing that module's section and comparison lemmas.

Let `f : Y ⟶ X` and `g : Z ⟶ X` be open immersions, and let `M` and `N` be
actual module sheaves on `Y` and `Z`. Given a single isomorphism `φ` between
their actual pullbacks to the scheme pullback `Y ×_X Z`, `glued` is a module
sheaf on `X`. It is the categorical pullback of the two restriction maps from
`f_* M` and `g_* N` to the pushed-forward overlap module. `overlap` expresses
`φ` on restrictions using the canonical restriction-to-pullback isomorphisms.

The constructions `leftIso` and `rightIso` identify the actual pullbacks of
`glued` with `M` and `N`. No covering assumption is needed for these
identifications. On an open contained in the image of `f`, the restriction map
from the right pushed-forward piece to the overlap is bijective; hence the
projection from the compatible-pair pullback to the left piece is bijective.
The analogous argument applies on the image of `g`. The proof uses preservation
of limits by the sections functor, the fact that the pullback of an isomorphism
is an isomorphism, and the restriction adjunction's counit. The generic
`restrictProj` construction and its section formulas implement this last step.

Write `p : Y ×_X Z ⟶ Y` and `q : Y ×_X Z ⟶ Z` for the projections.
The theorem `compatible` proves the actual module-morphism equation

```
p*(leftIso.hom) ≫ φ.hom = squarePullbackIso.hom ≫ q*(rightIso.hom).
```

Here the square comparison goes from `p* f* glued` to `q* g* glued` and uses
`p ≫ f = q ≫ g`. Thus the chosen comparisons realize the supplied overlap
isomorphism. To prove the equation, `proj_condition_apply` reads the categorical
pullback condition on sections, and `relation_restrict` restricts it to every
open of the overlap. The generic section formulas for `restrictProj` and the
published `restrict_square_ext` give `restrict_compat`. Finally the published
`pullback_compat_of_restrict` transports that equality to actual pullbacks.

All schemes lie in an arbitrary universe `u`. The construction needs no
Noetherian, integrality, finiteness or covering hypotheses. It constructs a
module sheaf, and makes no rank-one or complement-extension claim. In the host
extension argument it supplies a separate binary-gluing prerequisite; the
local extensions, coherent chart enlargement and final coverage argument
remain additional obligations.
