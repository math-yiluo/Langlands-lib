# The E₆ branch Levi factorization from the distinguished vertex

Assume the short-arm vertex is distinguished for every simply connected
absolutely almost-simple E₆ group over a totally complex number field.
Matching the branch cocharacters of the given group and its pure twist
gives a cocycle of the actual centralizer of the branch line on a finite
Galois refinement.

The centralizer is connected reductive, and its actual derived group is
simply connected. The geometric pinning of the derived group has the
complementary A₅ Cartan diagram. Each almost-simple factor over the
separable closure supplies a simple vertex, and consecutive vertices of
the A₅ chain lie in the same factor. The derived group is therefore
absolutely almost simple. Its cocenter in the centralizer is the split
quotient described in `TypeE6BranchLeviCocenter`.

`TypeE6BranchCentralizerCocycle.exists_leviFactorization` also proves that
the derived group has trivial star action if the ambient index's maximal
torus is split over the ground field. The derived torus after base change
is closed in the ambient torus, so restriction of split-torus characters
is surjective. Every geometric character of the derived torus is thus
Galois-fixed. This gives trivial star action on its pinning and, by
independence of the pinning, on the given index of the derived group.

Combining this factorization with `NumberFieldTypeE6LeviReduction` gives
vanishing over totally complex number fields from the stated marking
and the outer type A Hasse kernel. The construction corresponds to the
branch Levi reduction in Platonov and Rapinchuk, *Algebraic Groups and
Number Theory*, §6.8, printed pp. 382–383 and 385.
