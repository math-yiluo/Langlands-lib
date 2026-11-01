# Arithmetic covariance of actual normalized constant terms

Worker 2. Internal derived construction from `AdeleQuotientTransport`,
`ConstantTerm`, and `AmbientArithmeticTransport`, with the probability
uniqueness theorem for additive Haar measures in pinned Mathlib. There is no
new identification with original literature.

For actual number fields `K` and `L` in independent universes and a field
isomorphism `e : K ≃+* L`, `AdeleQuotientTransport.matrixEquiv a b e` applies
the actual continuous additive quotient equivalence to every entry of an
`a × b` matrix. Its forward and inverse continuity use the product topology.
The representative formula reduces it to entrywise arithmetic transport on
adelic matrices. Identity, covariant composition and inverse laws follow
entrywise.

With explicit compactness parameters for `AdeleQuotient K` and
`AdeleQuotient L`, arithmetic transport pushes the existing quotient and
matrix-quotient Haar probability measures to the corresponding measures
over `L`. The pushforward is an additive Haar measure and a probability
measure, so Mathlib's uniqueness theorem proves equality. All these measures
use their Borel sigma algebras; the local measurable instances introduce no
global instances. No Hausdorff hypothesis is added.

`integral_matrixEquiv` is the resulting change-of-variables formula for
complex Bochner integrals. `adelicEquiv_blockUnipotent` identifies the actual
arithmetic transport of the fixed standard block-unipotent embedding.
`constantTermIntegrand_arithmeticComap` then identifies the existing
lift-independent integrands by reducing to an adelic representative. Their
complex values are unchanged.

`constantTerm_arithmeticComap` proves that the normalized constant term
of arithmetic pullback at `g` is the old constant term at `adelicEquiv n e g`.
The split has the same arbitrary natural block sizes and the same equation
`a + b = n`. Applying this formula for every nontrivial split and using
surjectivity of the actual adelic group equivalence proves
`isCuspidal_arithmeticComap_iff`. It preserves and reflects exactly the
existing `IsCuspidal` condition, without any automorphic occurrence,
spectral existence or representation classification assertion.

`CuspidalContinuousFunctions.arithmeticEquiv n e` restricts the existing
continuous complex-linear ambient equivalence to the existing cuspidal
subspaces. Their full image equality follows from preservation, reflection
and ambient surjectivity. The topology remains the inherited compact-open
topology. Forward and inverse evaluation, identity, contravariant
composition, inverse and full right-translation covariance are proved.
The existing `CuspidalContinuousFunctions` alias is reused from
`CuspidalDeterminantMultiplier`. Finally `isCuspidal_complexConj_iff`
specializes the general result to actual CM argument conjugation with
complex values fixed.
