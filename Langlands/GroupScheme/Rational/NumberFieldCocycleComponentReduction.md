# Moving one component of a factored cocycle through a twist

`Cocycle.isTrivial_of_component_cocycles` implements the componentwise step of
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8,
printed pp. 374–375. In their trialitarian case the first subgroup has type
`A₁` and the second has type `A₁ × A₁ × A₁`. The lemma works with supplied
group homomorphisms and an action identifying the specified conjugations.

The action of the second coefficient group defines a twist of the first
subgroup. Since it fixes the image of the first coefficient group, the
first coefficient map into the twist descends over the original field.
The first cocycle remains trivial at the real places under this map.
Simple connectedness of the twist supplies triviality at the finite and
complex places. A supplied Hasse kernel for the forms of the first subgroup
makes its image trivial.

`Cocycle.isTrivial_of_component_cocycles_with_firstMap` passes the
descended map to the kernel argument. Its base change to the coefficient
field is the original first map followed by the twisting isomorphism.

A cochain that trivializes the second cocycle in the ambient group corrects
the inverse charts of the twisted subgroup. The corrected charts agree on
every double overlap and descend to one homomorphism into the ambient group.
The image of the first cocycle under this homomorphism is the twist of the
original ambient cocycle by the same cochain. Triviality therefore gives a
cochain on the original finite Galois cover.
