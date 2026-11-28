# The arithmetic chart argument for split prime torsion

`AbelianInertiaArithmeticReductionStatement` assumes arithmetic regular local approximation,
strictly Henselian Kummer factorization, and tame conjugation along a regular local divisor.
Its conclusion is `SplitAbelianInertiaPowerConjugacyStatement`. For an abelian scheme over
the fraction field of a strictly Henselian DVR with invertible prime \(\ell\) and trivial
geometric action on prime torsion, it compares a loop and its \(q\)-th power for one natural
number \(q>1\) at every finite \(\ell\)-power torsion level. The conjugators are residue-linear
equivalences of the actual torsion modules and may vary with the level. The geometric point
is taken over an algebraically closed field.

## Lean proof

`splitTorsionModel` supplies an abelian model over a finitely generated subalgebra with
invertible prime and relative sections giving all prime torsion points over one larger
finitely generated subalgebra. Arithmetic approximation applied to the larger algebra
produces a regular local chart, its distinguished parameter, and a comparison trait preserving
the uniformizer. Naturality along a geometric path transfers exhaustion by sections to the
chart point. The actual prime torsion action on the chart is therefore trivial. A path also
compares the original geometric point with the projection of the comparison trait's point.
The residue field of the chart admits one cyclotomic power by `arithmeticCyclotomicPower`.

At each prime-power level, triviality on prime torsion makes the original and chart action
images finite prime groups. `weaklyUnramifiedDvrQuotientLift` supplies a loop over the comparison
trait that has the original loop's value in the original finite image. The tame conjugation
hypothesis, applied to the chart image, conjugates the image of the chosen loop to its
\(q\)-th power. The commuting scheme maps and equivariant pointed torsion comparisons identify
these two chart actions with the actions of the original element and its power.

`abelianInertiaQuasiUnipotent_of_arithmetic` combines this implication with the finite-separable
split-trait reduction and the characteristic-polynomial argument. It concludes the exact
`AbelianInertiaQuasiUnipotentStatement` under the same three arithmetic hypotheses.

## Source

Deligne, *Résumé des premiers exposés de A. Grothendieck*, SGA 7 I, Exposé I, §0.4.1 and
Variantes 1.3 and 1.4, uses arithmetic approximation and the residue action on the Kummer
tower to obtain power conjugacy. The Lean argument uses finite torsion covers directly and
chooses a loop over the comparison trait separately for each finite image. The uniform
exponent is obtained from one chart for the whole family of actions.
