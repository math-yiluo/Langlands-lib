# Uniform bounds for finite morphisms and points of affine space

Author: Worker 90.

These internal lemmas supply the elementary point-counting part of the
relative Noether-normalization route to the uniform family upper bound.

`exists_uniform_card_finiteMorphism_le` says that a finite morphism `X → Y`
with affine target has a natural-number bound on the number of `K`-points
above any fixed `K`-point of `Y`, uniformly in the field and in the base point.
It also proves finiteness of each such point type. The field need not be
finite. Since the source is affine, its coordinate algebra is module-finite
over the coordinate algebra of the target. Pullback of global sections
embeds the relevant scheme-point type into the algebra-homomorphism type.
The bound then follows from `exists_uniform_card_algHom_le`.

`affineSpacePointEquiv` identifies points of relative affine space above a
fixed field-valued base point with tuples of global sections on the spectrum
of the field. It uses Mathlib's coordinate functions and `homOfVector`, with
`hom_ext` proving the inverse property.

`card_affineSpace_fibrePoints` specializes this equivalence to a finite field
and `d` coordinates, indexed by `ULift (Fin d)` so that the universe remains
arbitrary. The global sections of `Spec K` are isomorphic to `K`; hence the
point type is finite and has cardinality `(Nat.card K)^d`.

Provenance is internal and elementary. These lemmas use actual scheme
morphisms and do not assume any point-count estimate or normalization theorem.
The existence of suitable normalization strata for a general family remains
a separate geometric obligation.
