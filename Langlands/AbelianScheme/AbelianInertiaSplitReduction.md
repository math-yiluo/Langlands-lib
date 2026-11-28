# Reducing Tate power conjugacy to trivial prime torsion

A finite separable extension of the fraction field splits prime torsion. The normalization of
the original strictly Henselian trait is again a strictly Henselian trait over which the prime
is invertible. Passing to a positive power lifts the element to this extension, and the
pointed comparisons of torsion modules transport all finite-level conjugacies back.

## Lean statement and proof

`SplitAbelianInertiaPowerConjugacyStatement` specializes finite Tate power conjugacy to the
case where the entire pointed fundamental group fixes prime torsion. It asks for one natural
number \(q>1\) for each group element, with conjugacy between the actions of that element and
its \(q\)-th power at every finite prime-power level. The conjugating equivalence may depend on
the level. `SplitInertiaPowerConjugacyReductionStatement` says that this special case implies
`AbelianInertiaTatePowerConjugacyStatement`.

`splitInertiaPowerConjugacyReduction` represents the given geometric point by its map of fields.
`finiteSeparableFiberSplit` supplies a finite separable subextension on which all geometric
prime torsion points are rational. The integral closure of the DVR in the extension is a DVR
with the new fraction field. Henselianity uses `IsDiscreteValuationRing.henselianLocalRing_integralClosure`
from the pinned WeilConjectures package. The residue field of the new DVR is algebraic over the
original separably closed residue field, so it is separably closed. Invertibility of the prime
follows by mapping the original unit.

The image of the pointed cover group fixes the prime torsion fibre. `Tate.exists_levelBaseChange_intertwiner`
transports the action on each finite torsion module through the actual pointed pullback and the
residue-linear comparison. `liftPowerToCover` lifts the original loop raised to the order of the
permutation group on the fibre of the splitting field cover. Applying the split case to this
lift gives a common exponent \(q\). At each level, the pointed comparison conjugates the actions
of the lift and its \(q\)-th power to the actions of the corresponding powers on the original
Tate level.

## Source

The reduction is the finite extension step in Deligne, *Résumé des premiers exposés de A.
Grothendieck*, SGA 7 I, Exposé I, Variante 1.3, p. I-6. Here the argument is expressed on the
actual multiplication kernel and actual finite étale fundamental group. The henselian DVR
normalization theorem is imported from WeilConjectures at commit
`a25955cde4f85f67bef3149a6efc3efe20c22132`.
