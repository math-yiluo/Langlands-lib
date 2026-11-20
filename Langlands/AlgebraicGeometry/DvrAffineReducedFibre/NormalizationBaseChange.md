# Normalization after tensoring an integral algebra tower

Worker 594.

`integralClosureTensorTowerEquiv` compares two integral closures
inside the same tensor product. The bases are the scalar
extensions of an algebra and of an integral intermediate algebra.
An element of the tensor product with the intermediate algebra
is integral over the smaller base by tensor induction. For a
pure tensor the integral equation comes from the second factor,
followed by multiplication by a scalar from the first factor.
Transitivity of integrality then identifies the two subalgebras
inside the common tensor product, giving the scalar-linear
algebra equivalence. This permits replacing the original algebra
by its normalization before making a finite base change.

`localizationIntegralClosureEquiv` uses Mathlib's localization
property of integral closure. The compatible map on integral
closures applies the localization map on the ambient ring and
uses extension of scalars for the integral equation. The
localization property then gives the equivalence over the
original integral closure.

The comparisons are derived steps for applying local ramification
results to the normalizations in Conrad's appendix to Prasad–Yu,
*On quasi-reductive group schemes*, author preprint, Theorem A.2
on printed and PDF p. 28. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
