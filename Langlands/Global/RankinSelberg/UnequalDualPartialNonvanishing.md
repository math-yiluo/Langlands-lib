# Passing dual nonvanishing to the integral classes

`UnequalDualPartial.partialDualWhittakerIntegral_ne_zero` concerns two
cuspidal vectors spherical outside \(S\), where \(S\) contains the exceptional
sets of their spectral presentations and the ramified finite places of the
additive character. At a spectral value where the outer dual Whittaker
integrand is integrable, nonvanishing of its full integral implies
nonvanishing of the integral over `unipotentIntegralClasses F (t + 1) S`.
The partial integral retains the full inner rectangular integration.

At a place outside \(S\), `dualSplit` combines the splitting of the ordinary
Whittaker functions with the Weyl inverse transpose formula. The long Weyl
element has spherical value one. The corresponding dual spherical factor has
the opposite character and the componentwise inverse of the original Satake
tuple. For the rectangular argument the normalized block identity
`sphericalWhittaker_inverseStandard_rectGL_zero_mul` factors out the spherical
value of the padded translate independently of the rectangular variable. The
smaller spherical factor is right invariant under the integral group. Together
with the local determinant multiplier, these give a constant scalar for each
torus translate of the integral classes at the new place. Left unipotent
invariance extends the calculation to every representative of an integral
class there.

If the partial integral were zero, every cell term at one added place would be
zero by this scalar identity. The quotient cell decomposition sums these
terms to the integral over the enlarged set. Induction gives zero on all
finite enlargements of \(S\). The sets exhaust the quotient, so convergence of
the restricted integrals for an integrable function gives zero for the full
integral.

This is a nonvanishing consequence of the unramified splitting used in
J. W. Cogdell, *Analytic Theory of L-Functions for GLₙ*,
`cogdell-2004-analytic-theory-gln`, printed pp. 206 and 220. The implemented
proof works with the spherical factors of the two original presentations and
uses the integral on each cell before taking the exhaustion limit.
