# Comparison of Eisenstein series and intertwining integrals by their twists

`EisensteinTwistComparisonStatement` takes a pointwise identity expressing one
inducing twist as a finite sum of twists for a second Iwasawa compact at the
same parameter. It gives the corresponding identities for the Eisenstein
series and the twisted intertwining operator. Each identity has its own
convergence hypothesis on the finite comparison family at the adelic point
of evaluation. The finite family may be empty.

For the series, evaluate the supplied twist identity at the representative
of each parabolic rational coset times the given adelic point. Summability
allows the finite sum to pass through the sum over rational cosets. For the
integral, evaluate the same identity at the representative used by the
intertwining integrand. Each integrand is integrated against the same measure
on the rational quotient of the target radical. Integrability allows the
finite sum to pass through the Bochner integral. At the target parameter,
twisting the normalized operator multiplies it by the inverse of its
normalizing exponential, leaving the intertwining integral for each compact.

The comparison is a derived consequence of the definitions of the two
operators in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2.2, p. 191, equation (2.1) and
the displayed formula for the twisted intertwining operator. The proof uses
the Library's rational-quotient measure and its actual representatives.
In particular it applies to the finite twist expansion from compacts with a
common infinite projection. That expansion and regularity bounds supplying
the convergence hypotheses are separate inputs.
