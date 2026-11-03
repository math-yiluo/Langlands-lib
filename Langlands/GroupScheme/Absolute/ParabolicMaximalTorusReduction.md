# Structural reduction for the singleton parabolic maximal-torus proof

Worker 1336.

This is an internal conditional reduction assembled from the published
group-scheme predicates and elementary transport lemmas. It defines
`ParabolicMaximalTorusStructuralInputs.{u}` and proves that these inputs
imply the exact `ParabolicMaximalTorusStatement.{u}`. It does not prove
that the inputs hold.

The input proposition is the conjunction of the exact rational maximal-torus
existence, maximality under field extension, Borel maximal-torus containment,
and containing-Borel connectedness statements. It also requires rational
conjugacy of maximal tori for every smooth affine connected group over an
algebraically closed field, and connectedness of the algebraic-closure
extension of every connected reductive group. The conjugacy clause uses
the underlying group-scheme `MaximalToriAreConjugate` interface. The last
clause is explicit because `IsConnectedReductive` itself records
connectedness over the original field. Neither clause is discharged here.

The proof first uses closedness of the parabolic in the affine ambient
group to make the parabolic affine. Rational maximal-torus existence
then chooses `f : T.toGrp ⟶ P` over the original field. The desired torus
embedding is `f ≫ i`, so its factorization through the parabolic is
literal composition.

After extension to the algebraic closure, the parabolic's defining Borel
factorization supplies a Borel of the ambient group inside the parabolic.
The containing-Borel input gives connectedness of this extended
parabolic. Field-extension invariance makes the chosen torus maximal in
it. The Borel maximal-torus input supplies one torus inside the same
parabolic that is maximal in the ambient group. Conjugacy inside the
extended parabolic, via
`MaximalToriAreConjugate.isMaximalTorus_comp`, therefore makes the chosen
torus ambient-maximal after extension. The reverse implication of
field-extension invariance proves ambient maximality over the original
field.

This route applies in every universe `u` and uses the actual algebraic
closure in that universe. It adds no assumption on perfectness or
characteristic. All structural facts listed in the input proposition
remain proof obligations before the conditional reduction can yield an
unconditional proof of the host statement. This module contains no new
literature assertion; its provenance is the described composition of
the imported proposition definitions and transport lemmas.
