# Two-twist isolation of a local gamma order

`TwoTwistGammaOrderIsolationStatement` is the order calculation used in the
Rankin–Selberg approach to unique-place supercuspidality. Henniart–Herb
(1995), §§8.16–8.17, compares partial pair Euler products by global
functional equations and ramified twists. This internal statement takes the
two comparisons as `ComparisonInputs` on a common place index. The index may
group upstairs places above each downstairs place.

The first comparison retains the archimedean block. The second retains that
block and the desired finite place. The exceptional sets can differ across
the two comparisons. At a fixed spectral point, each auxiliary gamma factor
must have order zero, as happens for a nonzero epsilon monomial. The order
of each side's archimedean product must be preserved between twists.

`twoTwistGammaOrderIsolation` invokes `globalFiniteGammaComparison` twice.
The first equality of germs compares the archimedean orders because the sum
of auxiliary orders vanishes. The second compares the sums of the
archimedean and distinguished orders. The archimedean sums are finite by
admissibility and equal by the first comparison and preservation. Cancelling
them gives equality of the distinguished orders.
