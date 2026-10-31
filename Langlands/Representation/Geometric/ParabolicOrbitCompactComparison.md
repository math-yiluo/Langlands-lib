# Actual compact orbit integration

This internal specialization applies `splitStagesCompactEquiv` to the actual
target parabolic, its Levi projection and section, the orbit stabilizer, and the
intermediate inverse-image subgroup. It retains every prime, actual finite
p-adic extension, supplied compatible topology, pair of block shapes and
permutation. The source coefficient contains the positive source induction half
modulus. The theorem needs neither minimality nor intersection refinements.

The accompanying `ParabolicOrbitHaarRatio` module proves that the nested inverse
conjugation on the actual intersection becomes ambient inverse conjugation under
`parabolicOrbitNestedIntersectionAmbientEquiv`. Haar-character transport then
identifies its factor with the inverse correction Haar character. Combining this
with `parabolicOrbitNestedKernel_haarChar` identifies the generic split-kernel
ratio with `parabolicOrbitStagesHaarRatio`: correction inverse divided by radical
inverse is radical divided by correction.

`parabolicOrbitIntegratedCoefficientEquiv` has identity underlying linear
equivalence. The proved ratio equality makes it equivariant from the generic
ratio-twisted nested section action to the actual integrated coefficient. It is
defined for every source-Levi representation and every complex source character.

`parabolicOrbitCompactComparison_exists` supplies a family of representation
equivalences from the target-Levi action on the radical coinvariants of the
actual compact orbit induction to compact induction from the actual stages
quotient of the integrated coefficient. The published actual measure-existence
theorem supplies two-sided regular Haar measures and a compatible locally finite
quotient measure. These measures are chosen once before quantifying over smooth
source representations. Compact open bases and closedness follow from the
supplied p-adic topology; smoothness of the inducing coefficient follows from
smoothness of the original representation and the open kernel of the positive
source half modulus.

For each smooth source representation the proof applies the generic
`splitStagesCompactEquiv` with these data, then induces the identity-linear
`parabolicOrbitIntegratedCoefficientEquiv` along the actual stages quotient.
Naturality for every source intertwiner follows from
`splitStagesCompactEquiv_natural`: evaluation of the induced coefficient
identification retains the same values and canonical nested coinvariant maps.
Thus one common measure choice provides a natural family on the entire smooth
complex source category, without admissibility or dimension restrictions.

These results are derived specializations of the imported constructions. This
module supplies the unnormalized compact comparison; insertion of the target
inverse half modulus and identification with the normalized refined induction
are supplied by the separate induction transport.
