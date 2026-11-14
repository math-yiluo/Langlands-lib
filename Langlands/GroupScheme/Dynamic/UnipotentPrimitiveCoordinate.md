# Primitive homogeneous coordinates on dynamic unipotent groups

Let `F` be a group-valued functor on commutative algebras over any commutative
ring `R`, corepresented by `B`, and let `χ : Gm → Spec B` be a cocharacter.
This module constructs the multiplicative Laurent orbit of the actual dynamic
unipotent quotient algebra and proves that every positive homogeneous algebra
generator is an additive coordinate. There is no local-ring, reducedness,
noetherianity, smoothness or characteristic hypothesis.

`unipotentFunctor` is the actual subgroup functor cut out by the unipotent ideal;
`unipotentCorepresentation` is its quotient-algebra corepresentation.
`orbitAlgHom` first applies `unipCoaction` and then evaluates all Laurent
coefficients at the original algebra point. Its compatibility with the base
ring follows from `isGrading_unipCoaction.map_algebraMap`. `orbitFun` is the
point classified by that algebra map, and `coord_orbitFun` records its formula.

The helpers `affinePoint`, `algHom_affinePoint` and `pointRing_affinePoint`
identify algebra points with their points over the affine test scheme.
`affinePoint_orbitFun` proves that the ambient point of `orbitFun` is conjugation
by `χ(T)` of the original point extended to its Laurent polynomial algebra.
The proof uses the actual quotient-coaction formula `unipCoaction_mk`, the
classifying-ring-map formula `pointRing_conj`, and evaluation at the universal
Laurent unit. Comparing ambient points and using the injective subgroup
inclusion then gives the monoid homomorphism `orbitHom`.

`coord_mul` applies the derived criterion
`GradedPrimitive.coord_mul_of_homogeneous_generator` to this multiplicative
orbit. Its assumptions are a positive natural degree, homogeneity of `x` in
that degree, and surjectivity of evaluation `R[X] → B/I` at `x`. Its conclusion
is additivity of the values of `x` on every algebra point. Bijectivity of that
evaluation map is not required for this conclusion.

Finally, `appTop_mul` proves the same identity on every test scheme over
`Spec R`, including nonaffine schemes. The equivalence `Corepresented.pointsEquiv`
respects multiplication and evaluates the functor on relative global sections;
`homEquiv_symm_pointsEquiv_apply` identifies its coordinate values with pullback
of the section corresponding to `x`.

This is derived internal content: it combines the published actual dynamic
coaction, relative-Spec point comparisons and the supported-orbit additivity
criterion in `GradedPrimitiveCoordinate`. It supplies no torus-equivariance,
Weyl-normalization, gluing or isomorphism-theorem conclusion.
