# Admissibility of the actual surviving intersection coefficient

This internal unit proves admissibility of the original normalized coefficient pulled back along the target-intersection section in a surviving represented geometric-lemma piece. The groups and maps come from the existing `GeometricLemmaIntersectionDatum D`. Its geometric source intersection parabolic is assumed to have full all-test range. The preceding `SurvivingIntersectionGeometry` unit derives the consequent full-source-Levi conjugation isomorphism from this assumption.

Write `T` for the literal ambient target intersection parabolic

`pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom`.

Its common Levi is the same intersection with `pointImage (l ≫ p)` in place of `pointImage p`. Both groups carry their subspace topologies from the original ambient rational-point group.

For a commutative coefficient ring `B`, an original `B`-linear source-Levi representation `σ`, and a smooth unit-valued character `δ` of the full source parabolic, `D.targetIntersectionCoefficientRepresentation δ σ` is the following actual action on the original carrier. Inflate `σ` along the original source Levi projection, twist by `δ`, and pull back along `D.targetParabolicPointsToSource`. That last map is the original inverse-orbit conjugation of the target-intersection section. The construction does not assume admissibility.

`continuous_targetIntersectionProjection` proves continuity of the original intersection Levi projection. It applies the published `continuous_pointImage_projection` to the closed composite `D.q' ≫ lQ ≫ q`, the actual intersection Levi and radical maps, and the datum's multiplication isomorphism. The three existing point-image identities transport this projection to `D.targetPoints_isSemidirectDecomposition`. A private congruence lemma handles equality of the actual subgroup domains and codomains; proof irrelevance then identifies their semidirect-decomposition proofs. This argument does not treat the intersection as a parabolic of the ambient group.

Over a Noetherian `B`, `targetIntersectionCoefficientRepresentation_isAdmissible` proves that this action is admissible whenever `σ` is admissible. The implemented argument has three steps:

1. The derived `survivingIntersectionConjugationEquiv` identifies the entire common target Levi with the entire original source Levi, so pullback preserves the source admissibility.
2. The actual target-intersection projection is continuous by the preceding theorem, surjective by its original Levi section, and open by the proved continuous split-projection theorem. Inflation along it therefore preserves admissibility. The existing `targetParabolicPointsToSourceLevi_eq` and the original coefficient-map comparison identify this inflated action with the actual restricted source projection.
3. The original full source character pulls back to a smooth character because the actual target-intersection map is continuous. The published scalar-twist admissibility theorem gives the positively twisted conclusion. Its Noetherian premise is retained.

The generic ring, field and group schemes, and coefficient carrier have independent universes `uR`, `u` and `uV`. The projection-continuity theorem omits unused Hausdorffness, ambient local compactness and nonarchimedean assumptions. The generic admissibility theorem omits unused Hausdorffness and local compactness while retaining the ambient group structure used by the split projection and conjugation arguments.

`RationalNormalized.universalTargetIntersectionCoefficient_isAdmissible` specializes to the original actual universal family. Its conclusion is exactly

`IsAdmissible ((inducingRepresentation r h hU σ).comp D.targetParabolicPointsToSource)`.

It uses the full positive source-parabolic normalization of the supplied actual inducing model, the complete original `RegularAlgebra r`, its proved Noetherian property, and the previously proved admissibility of the actual universal tensor. The represented and supplied source decompositions prove the same proposition, keeping their projections equal by proof irrelevance. No alternate coefficient algebra, smaller norm family or coefficient-admissibility premise is supplied. The original complex representation is required to be admissible; neither irreducibility nor supercuspidality is needed for this surviving-coefficient step.

The provenance is internal: the unit combines the derived full-source-Levi geometry with the existing original projection identity, represented projection continuity, open split-projection inflation, continuous conjugation, smooth scalar twists and actual universal tensor admissibility. It does not assert that the native stabilizer-kernel quotient has already been compared with this coefficient, or that its compact induction has been identified with the orbit Jacquet quotient. Quotient transport, the split-stages calculation, compatible measures and their actual hypotheses, adapted finite orbit geometry and the final global finiteness theorem remain separate obligations.
