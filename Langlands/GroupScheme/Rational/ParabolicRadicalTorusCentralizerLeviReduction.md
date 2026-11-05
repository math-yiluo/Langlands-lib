# Reduction to one suitable maximal torus of the supplied radical

Author: Worker 1463.

This is internal derived assembly infrastructure. It imports the unchanged
published proposition `ParabolicRadicalTorusCentralizerLeviStatement.{u}` and
does not prove that proposition unconditionally.

`ParabolicRadicalTorusInitialCentralizerLeviStatement.{u}` is an explicit
remaining existence obligation. For every field, connected reductive ambient
group, rational parabolic and supplied geometric solvable radical, it asks for
one maximal torus in that radical and an actual rational Levi in the parabolic
whose ambient composite represents the whole-torus centralizer. The choice of
maximal torus may depend on the supplied radical. Its witness includes the full
published `IsRationalLeviSubgroup` predicate, in particular the geometric
unipotent radical and actual Levi-first scheme multiplication isomorphism.

`ParabolicRadicalTorusCentralizerLeviReductionStatement.{u}` states that the
published `SolvableMaximalTorusConjugacyStatement.{u}`, together with this initial
existence assertion, implies the unchanged target for every supplied maximal
torus. The theorem `parabolicRadicalTorusCentralizerLevi_of_initial_torus` proves
that implication. The ambient group is affine, and the parabolic and radical
inclusions are closed, so the radical is affine. Smoothness, connectedness and
solvability are fields of its supplied radical predicate. Rational
maximal-torus conjugacy therefore applies inside the radical, and
`SubgroupConjugate.exists_rationalLevi_torusCentralizer` transports the initial
Levi witness to the supplied maximal torus.

The proof preserves the equality of the published centralizer subgroup functors
on all relative test schemes and refinements. Both structural inputs remain
explicit premises of this internal implication. No initial Levi, maximal torus,
conjugacy theorem or structural existence theorem is constructed here.
