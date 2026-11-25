# Proof of differentiation of the L² classes of cusp forms on GLₙ

The theorem
`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalFormClassDerivative`
proves exactly `GeneralLinearCuspidalFormClassDerivativeStatement` at the
statement's original universe. Its two form classes are given, not constructed.

## Implemented proof

**Pointwise derivative.** Keep the finite factor fixed and take the smooth
infinite slice of the finite-smooth rational function. In the real matrix
coordinates let `M` be the matrix of `X`. The path through an infinite point
with matrix `g` has matrix `g exp(tM)`. Its derivative at every real `t` is
`g exp(tM) M`. The coordinate extension of the slice is smooth at each of
these invertible matrices. The chain rule and the formula for
`smoothDifferential` identify the derivative with the differential of the
slice evaluated at the translated point. The existing evaluation formula
for a real generator of the finite-smooth enveloping action gives the same
identity on the full adelic group (`evaluate_exponential_hasDerivAt`).

**From pointwise derivatives to a norm derivative.** In an arbitrary
σ-finite measure space, consider curves `U(t), V(t)` of `L²` classes with
representatives `u(t,x), v(t,x)`. Suppose `∂ₜu = v` pointwise, `v` is jointly
measurable and continuous in `t` at every `x`, and `V` is norm-continuous
and norm bounded. For a fixed `z ∈ L²` the function
`(s,x) ↦ ⟪z(x), v(s,x)⟫` is integrable on the product of a bounded time
interval with the given measure space. To see this, in each time slice use
`|⟪z,v⟫| ≤ |z|² + |v|²` and the uniform bound on `‖V(s)‖₂`; the slice
estimates imply product integrability. The pointwise fundamental theorem
of calculus, Fubini, and the continuous linear functional `⟪z, ·⟫` give

\[
   \langle z,U(t)-U(0)\rangle
     = \int_0^t \langle z,V(s)\rangle\,ds
     = \left\langle z,\int_0^t V(s)\,ds\right\rangle.
\]

This equality for all `z` identifies the difference of classes with the
Bochner interval integral. The fundamental theorem of calculus for the
norm-continuous curve `V` then gives `HasDerivAt U (V 0) 0`.

**Application to the quotient.** The two witnesses in
`IsGeneralLinearFormClass` give continuous representatives on the quotient.
Evaluate the pullback identities at a representative of each coset to
transport the pointwise derivative above. Right translation is continuous
jointly on the quotient, and composing the two almost-everywhere equalities
with the measure-preserving translations identifies the translated classes
with the translated representatives. The published quotient `L²` orbit
map is norm-continuous, and each translation is a linear isometry, giving
the bound for the derivative curve. Second countability and local finiteness
of quotient Haar measure give σ-finiteness. This proves
`GeneralLinearFormClassDerivative.quotient_hasDerivAt_of_formClasses` for
any finite-smooth rational function and its genuine real differential with
supplied form classes. The two classes need not be cuspidal for this helper.
The translation at time zero is the identity.

**Restriction to cusp forms.** Forget from the operator realization to the
finite-smooth rational function. Its genuine Lie action is the restricted
real generator just used. The bounded cuspidal orbit has the same ambient
`L²` values as quotient translation. The difference-quotient convergence
criterion and the subspace topology lift the ambient derivative to the
cuspidal submodule.

## Provenance and limits

This is a proof of the derived comparison stated in the companion
`GeneralLinearCuspidalFormClassDerivativeStatement.md`. Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 6.6.4
(p. 172; PDF p. 186) and Theorem 9.7.3 (pp. 265–266; PDF pp. 277–278),
compare the Hilbert and automorphic form models. Unlike the boundedness
step at the start of the proof of Theorem 9.7.3 (which invokes Theorem
9.7.1), the implemented differentiation argument uses the given square
integrability of the function and its derivative, not rapid decay or
finite total measure. It does not prove existence of the form classes,
realization or equivalence of summands, or multiplicity one.
