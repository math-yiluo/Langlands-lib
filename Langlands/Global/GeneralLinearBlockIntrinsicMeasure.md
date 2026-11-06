# Intrinsic normalized Haar on the actual two-block quotient

This internal specialization keeps the original two-block unipotent subgroup
functor, its principal rational image, and the existing quotient homeomorphism
to matrices over the additive adele quotient. It works over an arbitrary number
field and retains compactness of that additive quotient. Empty blocks are
allowed.

The represented closed block subgroup gives closedness of its actual adelic
points and hence local compactness. The already established multiplicative
coordinate equivalence with additive adelic matrices proves commutativity of
the existing subgroup law. Thus intrinsic subgroup Haar is right invariant.

`normalizedBlockHaarMeasure` specializes the existing intrinsic subgroup Haar
normalization. Its factor is the inverse of the actual rational quotient mass.
The intrinsic normalized quotient pushes forward through the existing quotient
homeomorphism to the original `matrixQuotientHaar`. To prove this, each matrix
translation is lifted to an actual adelic subgroup point, and quotient right
invariance gives additive invariance of the pushforward. Both measures have
mass one. Uniqueness of Haar on the compact additive matrix group removes the
scalar factor and gives equality.

Consequently the intrinsic normalized rational quotient measure is exactly
`rationalQuotientMeasure`, the measure already used by the original GL constant
term comparison, after the following explicit identification. The intrinsic
construction uses the inherited quotient sigma-algebra; the original measure
uses the Borel sigma-algebra. The proved `rationalQuotientBorelSpace` identifies
these sigma-algebras. The theorem
`normalizedRationalQuotientHaarMeasure_eq` therefore states equality of the
pushforward of the intrinsic measure under the identity map into the Borel
quotient with the original measure. Its proof uses injectivity of pushforward
under the quotient homeomorphism and the two exact matrix-measure identities.
It does not assert that the two sigma-algebras are definitionally equal.

`rationalQuotientMeasure_isCompatible` uses this equality to transfer the
existing counting-measure Weil compatibility theorem. Its ambient measure is
`normalizedBlockHaarMeasure`, its rational subgroup measure is counting
measure, and its quotient measure is the original `rationalQuotientMeasure`.
Thus nonzero regularity, positive right-translation invariance, integrability
of the quotient average of compactly supported continuous complex functions,
and the exact Weil integral formula all use the same normalization. The
private transport lemma eliminates the proved equality of sigma-algebras and
then applies the identity pushforward law.

This is an internal specialization derived from the imported actual block
coordinates and quotient homeomorphism, represented closed subgroup,
intrinsic subgroup Haar, quotient invariance and compact Haar uniqueness in
Mathlib. Compactness of the additive adele quotient remains the explicit
premise for the probability, equality and compatibility results. No
normalization choice or additional measure identity is assumed. The module
asserts no classification of parabolics, radical maximality or cuspidality
comparison, and does not discharge the general reductive finite-volume or
reduction-theory obligations.
