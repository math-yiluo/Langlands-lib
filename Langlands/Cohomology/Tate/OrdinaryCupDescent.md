# Bilinear descent through actual homology

This module provides an internal algebraic construction for the ordinary cup
product. It uses Mathlib's actual short-complex homology objects and universal
cokernel maps. Its constructions are valid over every commutative ring `R` in an
arbitrary common universe `u`, with no flatness or finiteness assumptions.

For short complexes `S` and `T` of `R`-modules and a target module `D`, a bilinear
map `β : S.cycles →ₗ[R] T.cycles →ₗ[R] D` descends when it vanishes on the image
of `S.toCycles` in its first argument and of `T.toCycles` in its second argument.
`descRight` uses `ShortComplex.descHomology` in the second argument. Surjectivity
of the canonical cycle projection proves additivity and scalar compatibility in
the first argument, producing `descRightLinear`. `descBilinear` then uses the
first cokernel universal property. `descBilinear_π_π` proves that evaluating the
result on the classes of two cycles recovers `β` on those cycles.

The second part specializes this construction to the actual inhomogeneous
cochains and `groupCohomology` of arbitrary representations `A`, `B`, and `C` of
a group `G : Type u`. For natural degrees `p` and `q`, a bilinear cochain map
from degrees `p` and `q` to degree `p + q` is supplied with three explicit kinds
of evidence:

- `hz` says its value on two cochains killed by their differentials is killed by
  the target differential.
- `hl` supplies an actual target boundary witness when the first argument is
  the incoming differential of a cochain and the second argument is a cocycle.
- `hr` supplies an actual target boundary witness with the arguments reversed.

Here an incoming differential means the first map of Mathlib's degreewise short
complex. This formulation includes degree zero, where that incoming map is
zero. The target witness consists of a natural degree `i` and a cochain in that
degree whose actual complex differential is the specified product.

`onCocycles` restricts the supplied pairing to actual cocycles by `cocyclesMk`.
`i_onCocycles` gives its underlying cochain. `onCycleClasses` projects this
cocycle to actual group cohomology. The lemma `class_eq_zero_of_boundary` proves
that a cycle whose underlying cochain is a differential has zero class: the
injectivity of the cycle inclusion identifies it with `toCocycles`, and the
composition of `toCocycles` with the homology projection is zero. Applied to
`hl` and `hr`, this gives the two vanishing conditions for `descBilinear`.

The resulting definition `fromCochains` has codomain
`groupCohomology C (p + q)` and is linear in both actual group cohomology inputs.
Its certificate `fromCochains_π_π` identifies the product of two classes with the
class of the supplied pairing on their cocycle representatives. The inclusion
certificate `i_onCocycles` identifies that representative with the original
cochain pairing.

This is a self-contained internal derivation from the kernel and cokernel
universal properties implemented by the pinned Mathlib API. It does not claim
to translate an additional theorem from the original literature. Worker 211
implemented all declarations and this explanation. This helper does not itself
define `ordinaryCup`: the later specialization must supply the explicit ordinary
cochain formula, and discharge `hz`, `hl`, and `hr` using its proved Leibniz
identity. It establishes neither the ordinary/Tate comparison nor any connecting
map compatibility law.
