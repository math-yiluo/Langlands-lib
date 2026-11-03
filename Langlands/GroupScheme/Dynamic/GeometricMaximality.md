# Geometric maximality from a reductive dynamic centralizer

This internal construction works over an arbitrary field and in every universe.
Let `χ` be a cocharacter of an affine group scheme `G`, let `p : P → G` be a
closed representative of its actual dynamic parabolic, and let `r : U → P`
have composite `r ≫ p` representing the actual identity-limit subgroup. Let
`z : Z → G` be a closed representative of the actual dynamic centralizer.
All representation and range conditions concern every test scheme, including
nonreduced schemes.

If `Z` has trivial ground-field unipotent radical, `normalUnipotentFactor`
constructs an actual group-scheme morphism `V → U` for each smooth connected
normal unipotent closed subgroup `v : V → P`. The all-test maximality theorem
of `Dynamic.SubgroupMaximality` places the ambient range of `v ≫ p` in `U(χ)`.
The published factorization through a represented subgroup then constructs the
morphism. Its composite with `r` equals `v`, by cancellation through the monic
representative `p`. Taking points on each original test scheme proves range
containment in the range of `r`.

If instead `Z` is connected reductive over the ground field,
`geometricNormalUnipotentFactor` performs this construction over its algebraic
closure. The field `hasTrivialGeometricUnipotentRadical` of that reductivity
predicate supplies exactly the radical hypothesis on the base-changed `Z`.
The actual dynamic parabolic, centralizer and identity-limit functors commute
with base change, as do their arbitrary representatives and closed inclusions.
Thus the same construction applies to every smooth connected normal unipotent
closed subgroup of the base-changed `P`, even when that subgroup does not descend
to the ground field. Its factorization equation gives precisely the greatestness
clause of `IsGeometricUnipotentRadical`.

The final assembly lemma combines this greatestness with closedness, smoothness,
connectedness, unipotence and normality of `r` over the ground field and with
connectedness and unipotence after base change. Geometric normality follows from
base change of normal subgroup functors. These structural conditions remain
explicit hypotheses of this internal adapter; it does not prove unipotence or
connectedness of the identity-limit subgroup, reductivity of its centralizer, or
the full dynamic radical or semistandard intersection theorem.

The construction and proofs are internal consequences of the stated existing
Library results, the definitions of connected reductivity and the geometric
radical predicate, and monic cancellation. They use no additional external
structural assertion, characteristic hypothesis, perfectness hypothesis or
restriction on the test schemes.
