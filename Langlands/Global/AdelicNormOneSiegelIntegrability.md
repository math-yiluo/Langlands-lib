# Integrability from simple-root logarithms on a fixed norm-one Siegel chart

`AdelicNormOneSiegelIntegrabilityStatement` fixes a connected reductive number-field
group and an algebraic Siegel setup. For that setup it chooses compact factors, a
weak chamber threshold, a finite family of norm-one right translates, an exponent
`d` and a finite constant `L`. If a measurable rationally invariant nonnegative
function is bounded at the resulting chart points by
`B δ(a) (siegelRootLogSize a)⁻ᵈ`, its integral on the norm-one rational quotient is
at most `B L`. Here `δ(a)` is the minimal Siegel modulus and `siegelRootLogSize a`
is one plus the sum of the absolute simple-root logarithms of the torus point `a`.

The proof takes a compact neighborhood of the identity in the positive split
center and extends the function to the full group by the norm-one projection,
multiplied by the indicator of that neighborhood in the central coordinate.
The positive central factor and the norm-one factor of a Siegel point give the
two arguments of this extension. The absolute dyadic indices on its support
have sum bounded by an affine function of `siegelRootLogSize a`. This follows
from `abs_intLog_two_le` for both sets of characters and boundedness of the
central logarithms on the compact neighborhood.

`exists_lintegral_centralSiegelSet_le` cancels the modulus in the pointwise
majorant against the inverse-modulus factor in each dyadic volume estimate.
The remaining weights are summable with `d` equal to twice the number of
dyadic coordinates, by `SiegelSetMeasure.tsum_decay_ne_top`. The finite chart
cover and the quotient unfolding inequality carry the bound to the full
rational quotient. Finally `measurePreserving_rationalQuotientDecomposition`
expresses its integral as the product of the norm-one integral and the
positive finite mass of the central neighborhood. Dividing by that mass
gives the stated uniform bound.

The estimate uses the same modulus cancellation as the Siegel-domain
integral quoted in Delorme's (2.5). The choice of root logarithms and the
central cutoff give a norm-one criterion for a prescribed algebraic setup.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF §2, (2.5), and §3.4, Lemma 3.10(i).
