# Actual stalk quotients of closed immersions

For an actual closed immersion `i : X ⟶ Y`, a point `x : X`, and an affine
open `U` of `Y` containing `i x`, `ker_stalkMap_eq_map` identifies the kernel
of `O_{Y,i(x)} → O_{X,x}` with the extension of
`ker(Γ(Y,U) → Γ(X,i⁻¹U))` along the germ map.
`quotientStalkAlgEquiv` constructs the corresponding algebra equivalence
from the quotient of `O_{Y,i(x)}` to the actual stalk `O_{X,x}`. Its base
algebra structure is the actual stalk map of `i`. All schemes use the
arbitrary universe `u`.

The proof uses the affine preimage of `U`, which is affine because a closed
immersion is affine. Both germ maps are localizations at the primes of
the two chosen points. Mathlib's `IsAffineOpen.comap_primeIdealOf_appLE`
identifies the primes under the section map. Surjectivity of that section
map identifies the image of the source prime complement with the target
prime complement. `IsLocalization.ker_map` then computes the localized
kernel. The germ compatibility of the actual scheme morphism identifies
this localization map with its actual stalk map. Finally, surjectivity
on stalks and the first isomorphism theorem for algebras give the stated
quotient equivalence.

This is an internal derived comparison for formal line-bundle effectivity.
It applies to arbitrary closed immersions and requires no noetherian,
properness, completeness or flatness assumption. It does not calculate
the affine kernel for a specified adic thickening, identify a module
pullback stalk, or prove coherent algebraization.
