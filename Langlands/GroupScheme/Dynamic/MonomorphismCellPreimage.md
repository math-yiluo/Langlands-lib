# Inverse images of dynamic triple cells under monomorphisms

This is an internal construction and proof derived from the Library's dynamic
subgroup functors, represented subgroup maps, base-change point equivalence,
closedness of field monomorphisms, and open triple cells. No separate translation
of an external source is asserted.

Let `S` be any scheme, `f : H ⟶ G` a homomorphism of group schemes, and
`χ : Gm_S ⟶ H` a cocharacter. Write `χ_G = χ ≫ f`. Choose inclusions
`iM`, `iZ`, `iU` representing `U_H(-χ)`, `Z_H(χ)`, `U_H(χ)` and inclusions
`jM`, `jZ`, `jU` representing `U_G(-χ_G)`, `Z_G(χ_G)`, `U_G(χ_G)`.
Here the negative cocharacter means precomposition with `Gm.powerHom S (-1)`.
The represented subgroup conditions concern every scheme over `S`.

The definition `tripleCellFactor` is the product of the three actual restriction
homomorphisms induced by `f`, with the association `M × (Z × U)`. Its construction
has no smoothness, affineness, connectedness, or monomorphism hypotheses.
`tripleCellFactor_comp` proves that its composite with the target triple-cell
multiplication is the source triple-cell multiplication followed by `f`.

For the main comparison, suppose both structural morphisms `H → S` and
`G → S` are smooth and affine, the former is geometrically connected, and
`f.hom.hom` is a monomorphism in schemes over `S`. Then
`preimage_range_tripleCellMultiplication` proves the equality of sets of points

```
f⁻¹(range(U_G(-χ_G) × (Z_G(χ_G) × U_G(χ_G)) → G))
  = range(U_H(-χ) × (Z_H(χ) × U_H(χ)) → H).
```

The maps inside the ranges are the actual represented triple-cell multiplication
maps. `isPullback_tripleCellFactor` proves that the commuting square consisting
of `tripleCellFactor`, these two multiplication maps, and `f` is a pullback
square of schemes. This is a scheme-level cartesian assertion, including the
scheme structures, rather than only a comparison of field-valued points.
The statements hold in every universe and impose no condition on the base.

Two intermediate lifting results use weaker target hypotheses: `G → S` need
only be affine and locally of finite type. Their source hypotheses are smoothness,
affineness, and geometric connectedness, together with monicity of `f`.
`exists_triple_factors_over_fieldPoint` treats a field `K`, a map `Spec K → S`,
and every scheme `T → Spec K`. If an `H`-point of `T`, regarded over `S`, has
image decomposed into prescribed target dynamic factors, it has corresponding
source factors with those prescribed images and the same ordered product.
`exists_tripleCell_lift_over_fieldPoint` packages this as a lift into the source
represented triple cell whenever the image has a lift into the target cell.

The field-test proof base changes to `Spec K`. The smooth affine geometrically
connected source becomes a smooth connected affine group over `K`, so
`HomImage.isClosedSubgroup_of_mono` makes the base-changed homomorphism closed.
The opposite/triple-factor lifting theorem for closed subgroups therefore
applies on every `T`. The multiplication-compatible `baseChangePointsEquiv`,
cocharacter base-change identities, and base-change identities of the dynamic
subgroup functors transport the factors, their membership, images, and product
back to points over `S`. The represented version lifts each source factor using
`pointsEquiv` and combines them by the cartesian product universal property.

For the range equality, take any point `x` of `H` whose image lies in the target
cell. The residue-field morphism `Spec κ(x) → H`, followed by `f`, has all its
points in that cell. Since the target cell is an open immersion, this morphism
lifts into it. The field-test result then lifts the residue-field point into the
source cell. Evaluation at the closed point of `Spec κ(x)` puts `x` in its
range. The reverse inclusion follows by evaluating `tripleCellFactor_comp`.
Both cell multiplications are open immersions by the arbitrary-base triple-cell
theorem. Their range equality and commuting square then give the asserted
pullback by the open-immersion pullback criterion.

This unit does not prove closedness of the three-factor map or the global
reductive monomorphism closed-immersion theorem. Those conclusions require
further inputs.
