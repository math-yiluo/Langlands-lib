# Relative unipotent maps with arbitrary affine representatives

This is an internal transport of
`Corepresented.RelativeUnipotent.isClosedImmersion_unipotentMap` from
`Dynamic.UnipotentMonomorphism`. It uses the affine coordinate equivalences
and the represented-subgroup transport in `Dynamic.AffineRepresentability`.
It makes no separate claim of correspondence with an external source.

Let `R` be any commutative ring, `G` and `H` group schemes over `Spec R`,
`χ : Gm → G` a cocharacter, and `f : G → H` a group-scheme homomorphism.
Suppose `i : U → G` represents the dynamic unipotent subgroup functor
`unipotent χ` and `j : V → H` represents `unipotent (χ ≫ f)`. These
representation hypotheses mean that the inclusions are monomorphisms over
the base and have exactly the prescribed points on every test scheme.
They do not assume that the inclusions are closed.

`Dynamic.unipotentFactor χ f hi hj : U → V` is the unique factor of
`i ≫ f` through `j`. The construction uses functoriality of the actual
orbit-contraction condition, and `unipotentFactor_comp` proves its
commuting square
`unipotentFactor χ f hi hj ≫ j = i ≫ f`. This construction does not
require either ambient group to be affine or `f` to be monic.

If both ambient groups are affine and `f` is a monomorphism of schemes
over `Spec R`, `isClosedSubgroup_unipotent_of_represented` proves that
every homomorphism `g : U → V` with `g ≫ j = i ≫ f` is a closed
immersion. In particular, `isClosedSubgroup_unipotentFactor` proves
closedness of the constructed factor. `IsClosedSubgroup g` is the
closed-immersion property of the underlying scheme morphism; no
normality claim is made.

The auxiliary theorem
`Corepresented.RelativeUnipotent.isClosedSubgroup_of_represented`
first proves this assertion for corepresented affine ambient groups.
Uniqueness of representatives gives isomorphisms from `U` and `V`
to the canonical quotient-coordinate unipotent groups. Cancellation
against the target inclusion shows that `g` becomes the canonical
`unipotentMap`. Its closedness follows from the imported theorem and is
transported along these isomorphisms.

For general affine ambient groups, the proof chooses
`AffineCoordinates.groupSchemeIso`, transports the cocharacter,
homomorphism and represented inclusions to corepresented coordinates,
and applies that auxiliary theorem. Ambient isomorphisms preserve
monicity and carry the dynamic unipotent functors to their inverse-image
functors, so the supplied hypotheses provide precisely the transported
representation and monicity data.

All results are universe polymorphic and hold over arbitrary `R`.
There are no smoothness, flatness, finite-type or finite-presentation
assumptions. This module supplies the relative unipotent step toward
reductive monomorphism closedness; the cell, torus and remaining global
arguments are separate obligations.
