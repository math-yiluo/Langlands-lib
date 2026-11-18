# Reduction of tensor units to bounded inverse pairs

Worker 287, 17 November 2026; premise switched to the published
statement by Worker 5678, 18 November 2026.

This internally derived algebraic reduction has an explicit finiteness premise,
the published Library statement
`Langlands.Algebra.RosenlichtBoundedInversePairsStatement.{u,w}`: normalized
inverse pairs in finite-dimensional subspaces of any domain with an
augmentation to an algebraically closed ground field form a finite set. The
premise is a `Prop`-valued definition used as a hypothesis, not an axiom.

`Langlands.Algebra.Rosenlicht.tensorUnits_of_boundedInversePairs` proves that
this premise implies exactly
`Langlands.Algebra.RosenlichtTensorUnitsStatement.{u,v,w}`. The final theorem
`Langlands.Algebra.rosenlichtTensorUnits` supplies the premise using Worker 565's
implemented bounded inverse-pair proof.

The reduction chooses an augmentation of the second algebra by the finite-type
point-existence lemma. Evaluation of the tensor unit gives a unit of the first
algebra. Dividing by that unit's tensor-factor image normalizes the tensor and
its inverse to have augmentation one. Tensor induction bounds their rational
specializations in two finite-dimensional subspaces of the second algebra.
The finiteness premise makes these specialization pairs a finite set. The
point-detection and domain argument in `RosenlichtSpecialization` makes the
normalized tensor family constant. A rational point of the first algebra
exhibits this constant as an actual unit of the second algebra. Undoing the
normalization gives the required pure tensor of actual units.

The direct imports are `Langlands.Algebra.RosenlichtTensorUnitsStatement`,
`Langlands.Algebra.RosenlichtBoundedInversePairsStatement` (both unchanged
published statements) and `Langlands.Algebra.RosenlichtSpecialization`. The
field and two algebra universes remain independent. Rational points are obtained within the proof;
none is added to the final statement's hypotheses.
