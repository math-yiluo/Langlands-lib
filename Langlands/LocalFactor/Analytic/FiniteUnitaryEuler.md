# Finite unit-circle Euler products

This internal construction stores a real spectral base `q > 1` and a finite set
of complex parameters, each of norm one. Its normalized polynomial is the product
of `1 - a X` over those parameters. The entire denominator evaluates that
polynomial at `exp(-s log q)`; `reciprocalEntire` retains its punctured reciprocal
germs, and `reciprocal` is an ordinary complex-valued representative.

The denominator is analytic by finite products of analytic exponentials. If
`Re(s)` is nonzero, the norm of the spectral parameter differs from one.
Consequently no factor `1 - a q^(-s)` vanishes. In particular evaluation at
`s = 1` shows that the entire denominator is not identically zero.

At every complex point the reciprocal is meromorphic with nonpositive, finite
order. The proof uses the identity principle in
`ReciprocalEntire.denominator_eventually_ne_zero` to exclude an infinite
denominator order, then negates its nonnegative analytic order. Away from the
imaginary axis the reciprocal is analytic and nonzero.

If the parameter set contains one, the denominator vanishes at zero. The
reciprocal then has strictly negative meromorphic order there: a nonnegative
order would supply an analytic representative of its punctured germ, contrary
to `ReciprocalEntire.isPole_iff_no_analytic_germ`.

For a family of these data, `basePairConditions` packages the analytic inputs of
`Global.PoleComparison.BasePairConditions`, provided each matched pair has
parameter one. No equality with a representation-theoretic L-factor is assumed
or proved here. That identification and the matched-pair parameter test remain
separate obligations. The construction derives from the published exponential
spectral parameter, reciprocal-entire identity principle, and Mathlib
meromorphic-order calculus; it makes no external literature claim.
