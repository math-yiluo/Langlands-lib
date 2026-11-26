# Cuspidal trace class from uniform bounds for convolution representatives

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalTraceClassFromUniformBoundStatement`
uses the actual full almost-everywhere cuspidal space \(S\) on the measured
positive rational quotient \(Q\). The group is a connected reductive affine
locally finite-type group scheme over a number field. The other data are
`ParabolicDynamicStatement`, a split central torus with injective, finite-index
character restriction, and right invariance of Haar measure on the norm-one
group. The operator \(R(f)\) acts inside \(S\) and integrates the original
right action with the chosen Haar measure on the full adelic group.

Assume that for every `IsAdelicTestFunction` \(f\) there is a nonnegative real
\(C_f\) such that each \(R(f)\phi\), for \(\phi \in S\), has a continuous
representative \(v\) satisfying

\[
  |v(q)| \le C_f \|\phi\|_2 \qquad(q\in Q).
\]

The representative agrees with the class almost everywhere for the
positive quotient measure. The conclusion is that \(R(f)\) is trace class
for every such test function. The bound is uniform in both \(q\) and \(\phi\)
and is assumed for all test functions, including the factors furnished by
Dixmier–Malliavin.

This is the cuspidal application of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Lemma 9.3.3 and (9.13), printed
pp. 247–248 (PDF pp. 259–260). The source formulates the estimate using
tests on \(A_G\backslash G(\mathbb A_F)\). The Library formulation uses
its own adelic tests and the Bochner integral on the full adelic group.
The split-centre action on the positive quotient is trivial. The finite
volume of \(Q\) comes from the Library's norm-one finite-volume theorem.
The continuous representatives give bounded evaluation functionals
by uniqueness for the full-support quotient measure. The Library's
uniform evaluation criterion yields Hilbert–Schmidt operators, and its
adelic convolution factorization yields trace class.

The uniform estimate in the hypothesis is the analytic input to the
trace-class argument. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
