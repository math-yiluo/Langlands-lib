# Deduction of Kottwitz's theorem from the trace comparison

`CMHarrisKottwitzDeductionStatement` is the implication from
`CMHarrisKottwitzTraceComparisonStatement` to the published Harris CM
proposition at the same two derived-category universes.
`cmHarrisKottwitzLambdaAdic_of_traceComparison` proves that implication.
The premise supplies the geometric Frobenius and virtual polynomial
comparison used below.

For each coefficient place, apply weight separation at the auxiliary place.
The separated occurrence test is equivalent to a positive characteristic
polynomial degree in some cohomological degree. This degree is the dimension
of the actual Hecke multiplicity space by the fixed-vector comparison and the
Frobenius characteristic polynomial identity. The higher-degree vanishing
clause extends the test to the range of all natural numbers.

At a chart place, monicity and positive degree of the Kottwitz polynomial
follow from its published polynomial comparison and the positive binomial
factors of the degree of the dual representation. The auxiliary coefficient
place supplies the virtual identity for this polynomial. Algebraic weight
separation gives pure factors over `K`. Each root of the original polynomial
is a root of one of the factors at the same embedding. The vanishing factors
of the wrong parity then give the required parity for this root.

For uniqueness, at one complex embedding extract the roots at the radius for
a single degree. This extraction is multiplicative on monic polynomials and
recovers precisely the factor in that degree, since the radii of different
degrees are distinct. Injectivity of the coefficient map gives uniqueness over
`K`. At any coefficient place the pure factors produced by separation are
therefore the same. Injectivity of the chosen complex realization descends
the characteristic polynomial identity to `K_λ`. The Euler-polynomial
transport for the actual continuous Hecke multiplicity representation gives
the reverse of this polynomial under the target's continuity and finiteness
hypotheses.

This is the degree-separation argument of Kottwitz (1992), §6, printed p. 664,
in the Library's actual Harris CM telescope. The trace premise is documented
in the companion `HarrisTaylorCMKottwitzTraceComparison.md`.
