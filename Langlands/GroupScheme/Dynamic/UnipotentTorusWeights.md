# Torus weights on dynamic unipotent coordinate algebras

This is a derived internal prerequisite for the local split Isomorphism
Theorem. Let `R` be a commutative ring, let `F` be a group-valued functor on
`R`-algebras corepresented by an algebra `B`, and let
`i : splitTorus (Spec R) I ⟶ groupScheme F e`, where `I` is finite.
For an integer vector `ν`, write `χ` for the exponent cocharacter followed by
`i`. The algebra in this module is the actual quotient algebra of the dynamic
unipotent subgroup `U(χ)`. No injectivity assumption on `i` is needed.

`action` constructs conjugation by the full split torus on `U(χ)`, using
`Dynamic.unipotent_isStable_conjugation` and
`AutomorphicAction.onRepresentedSubgroup`. Its induced algebra-point action is
`torusAction`. The lemmas `action_act_comp`, `affinePoint_val` and
`affinePoint_act` identify this action, after inclusion in the ambient group,
with actual conjugation on every affine test algebra. The general helper
`UnipotentPrimitive.affinePoint_map` identifies change of algebra with
precomposition on affine points.

`torusPt_cocharacter` identifies the torus point with coordinates `u ^ ν j`
with the image of `u` under the exponent cocharacter. Consequently
`orbitFun_eq` identifies the Laurent orbit of `UnipotentPrimitiveCoordinate`
with the full torus action restricted along `χ`, after extending scalars to
the Laurent polynomial algebra. These are identities of algebra-valued
points, without passage to fields.

For a weight vector `m`, `exponentValue_unitT` computes the restricted
character as `T ^ (∑ j, m j * ν j)`. Applying the weight action formula at
the universal point and the preceding orbit comparison proves
`isHomogeneous_mem_homog`: a coordinate homogeneous of full-torus weight
`m` is homogeneous of degree `∑ j, m j * ν j` for the existing
`unipCoaction`.

The general lemmas `comp_grading_comp` and `comp_mem_grading_homog` apply
to any torus action and Laurent grading for which every homogeneous torus
weight lies in a specified grading degree. They expand a coordinate in its
finite torus-weight decomposition. Orthogonality of torus projections and
the formula for a degree projection on a homogeneous element show that
the two kinds of projections commute. Therefore each torus projection
preserves every homogeneous degree. `comp_mem_homog` applies this argument
to the actual dynamic unipotent coaction using the dot-product degree
just proved.

Now assume `R` is local, including its usual nontriviality assumption.
Given a coordinate `x` of positive natural degree `d` for `unipCoaction`,
and bijectivity of `Polynomial.aeval x : R[X] →ₐ[R] coord(U(χ))`,
`exists_isHomogeneous` proves that `x` has a full-torus weight. It applies
`TorusStableLine.exists_isHomogeneous_of_preserves_degree` to the proved
degree preservation; there is no additional stability premise.
`coordinateWeight` chooses such a vector, and
`isHomogeneous_coordinateWeight` proves that this selected vector is
the actual weight of `x`. Thus the existing
`coord_act_of_isHomogeneous` formula applies to actual conjugation on
every algebra test.

The provenance is internal: the constructions combine `ActionStability`,
`RepresentedAction`, `TorusActionBridge`, `TorusGrading`,
`TorusStableLine`, `ExponentCocharacters`, the dynamic unipotent grading,
and the Laurent-orbit comparison in `UnipotentPrimitiveCoordinate`.
The proof retains nilpotents and uses no reducedness, noetherianity,
henselianity or characteristic assumption. It assumes a positive
homogeneous polynomial coordinate; it does not construct that coordinate
for every reductive group. Identification of the selected character with
a prescribed root, Weyl normalization, and the full local split
Isomorphism Theorem remain further obligations.
