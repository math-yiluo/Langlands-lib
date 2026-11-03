# Structural reduction for dynamic geometric unipotent radicals

This internal unit chooses an actual closed embedding of a represented dynamic
identity-limit group into a standard upper unitriangular group scheme. It then
combines the existing structural results to reduce the universal dynamic
geometric-radical proposition to three separately stated prerequisites.

The group schemes are the existing `Langlands.GroupScheme` objects. Their
subgroup functors and representation hypotheses range over every test scheme,
including nonreduced schemes. All fields and the universe parameter are
arbitrary.

## Chosen closed embedding and unipotence

For an affine locally finite-type group `G`, a cocharacter `χ`, and a closed
representative `j : U → G` of `Dynamic.unipotent χ`,
`unitriangularDimension` chooses a natural number from
`exists_closed_unitriangularEmbedding`. `unitriangularModel` chooses the
corresponding morphism to the standard upper unitriangular scheme, whose weights
are `i ↦ -i`. Its closedness is the corresponding witness from that existence
theorem.

`isUnipotent_of_unitriangular_inputs` assumes exactly
`UnitriangularUnipotentStatement` and `UnipotentClosedSubgroupStatement`. The first
makes the target of the chosen embedding unipotent. The target is affine and
locally of finite type because its inclusion into the smooth general linear
group is closed. The second prerequisite therefore makes `U` unipotent.

## Normality and geometric structure

`range_unipotentRepresentative_isNormal` treats arbitrary compatible
representatives `p : P → G` and `r : U → P` of the dynamic parabolic and
identity-limit subgroup. Conjugate a point of `U` by a point of `P`, use the
existing ambient normalization theorem, and lift the result through `r ≫ p`.
Cancellation through the monomorphism `p` proves that the lift gives the desired
conjugate in `P`. This argument works over any base scheme.

For a smooth affine group over a field,
`isGeometricUnipotentRadical_of_unitriangular_inputs` assumes the two unipotence
prerequisites and connected reductivity of a represented dynamic centralizer.
Closedness of the dynamic inclusions and cancellation of closed immersions give
closedness of `r`. The published dynamic smoothness and contraction connectedness
theorems supply smoothness and connectedness of `U`. The chosen embedding supplies
unipotence, and the preceding normality theorem supplies normality in `P`.

After base change to the algebraic closure, the ambient group remains affine and
locally of finite type. The actual base-changed composite represents the
base-changed dynamic identity-limit functor. Apply the same connectedness and
unipotence arguments there. Finally, the existing `GeometricMaximality` adapter
uses reductivity of the centralizer to supply geometric greatestness and combines
these clauses into the exact `IsGeometricUnipotentRadical r` predicate.

## Exact universal reduction and provenance

`dynamicGeometricUnipotentRadical_of_unipotence_centralizer` assumes the two named
unipotence propositions and `DynamicCentralizerReductiveStatement`. It chooses
the canonical affine centralizer representative and applies the previous
adapter. Its conclusion is exactly the existing
`DynamicGeometricUnipotentRadicalStatement` in every universe.

All constructions and proofs are derived internally from the imported
definitions and results. The three prerequisite propositions remain assumptions
of these reduction lemmas. This unit proves none of those prerequisites and does
not assert an unconditional proof of the full semistandard intersection theorem.
