# Adjoining a root of a DVR uniformizer

For a discrete valuation ring `R`, a uniformizer `π` and a positive integer `n`,
this module constructs the discrete valuation ring `R[X]/(X^n - π)`. The class
of `X` is a uniformizer. The quotient by the class of `X` is the residue field
of `R`, via evaluation at zero and reduction of the coefficients.

Each maximal ideal contains the class of `X` because its contraction to `R`
contains `π`. The polynomial is monic, so its root algebra is free over `R`.
The `n`th power of the class of `X` equals the image of `π`. Multiplication by
`π` is injective on the free module and therefore so is multiplication by the
class of `X`. The finite algebra is Noetherian, so its local ring is separated.
The separated local ring criterion then proves the DVR property. The
equivalence `integralClosureEquiv` uses integrality over `R` and integral
closedness in the fraction field.

This construction formalizes the uniformizer-root step used in tame ramification
elimination. It follows the ring construction in Lemma 15.116.2, with the same
argument covering degree one. [The Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
