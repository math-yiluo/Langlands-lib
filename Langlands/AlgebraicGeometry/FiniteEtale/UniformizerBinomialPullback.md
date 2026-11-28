# Pullback of a binomial cover at a uniformizer

A binomial cover stays connected after a pullback to the fraction field of a DVR when the
binomial is carried to \(X^m-\pi\) for a uniformizer \(\pi\) and a positive degree \(m\).

## Lean proof

`binomialCover` packages the usual finite étale morphism obtained by adjoining a root of
\(X^m-b\) when \(m\) and \(b\) are units. Finiteness uses the monic-polynomial basis, and
étaleness uses invertibility of the derivative in the adjoining ring.

`irreducible_uniformizerBinomial` derives irreducibility over the original DVR from the
proved domain property of its binomial algebra. Gauss's lemma then gives irreducibility over the
fraction field. For `uniformizerBinomialPullback`, the affine pullback is the spectrum of a
tensor product, and `AdjoinRoot.tensorAlgEquiv` identifies that tensor product with the ring of
the pulled-back binomial. This ring is a field, giving connectedness of its spectrum and hence of
the pullback. The connectedness assertion itself needs only the positive degree and the
uniformizer condition.

## Source

The Stacks Project, *Fundamental Groups of Schemes*, Example 58.31.4 (tag `0EYF`), gives the
standard finite étale binomial cover of the complement of a divisor when the degree is invertible.
The connectedness claim here is the DVR specialization of its base change, using the domain
result in `DvrUniformizerRoot`.
