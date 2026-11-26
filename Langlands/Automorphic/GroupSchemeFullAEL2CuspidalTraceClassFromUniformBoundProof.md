# Trace class from uniform evaluation on the full cuspidal space

The theorem
`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2CuspidalTraceClassFromUniformBound`
proves the proposition
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalTraceClassFromUniformBoundStatement`.
Its type is that proposition, with the same universe parameter.

## Setting

Fix the data of the statement and assume its hypothesis. Write \(Q\) for
`PositiveRationalQuotient F G T i` and \(\mu_Q\) for
`positiveRationalQuotientHaarMeasure F G T i`. Write \(S\) for the full
cuspidal subspace `fullAEL2CuspidalSubmodule`, \(j : S \to L^2(Q,\mu_Q)\)
for its isometric inclusion `fullAEL2CuspidalInclusionLI`, and \(R(f)\) for
`fullAEL2CuspidalIntegratedAction` with Haar measure on the adelic group.
The hypothesis says the following. For every adelic test function \(f\)
there is a constant \(C \ge 0\). Every \(R(f)\phi\) with \(\phi \in S\)
agrees \(\mu_Q\)-almost everywhere with a continuous function \(v\) such
that \(|v(q)| \le C\|\phi\|\) for every \(q \in Q\).

The proof first records three facts about the quotient measure:

- The quotient \(\sigma\)-algebra on \(Q\) is its Borel \(\sigma\)-algebra
  (`positiveRationalQuotient_borelSpace`).
- \(\mu_Q\) gives positive mass to nonempty open sets
  (`haarQuotientMeasure_isOpenPosMeasure`).
- \(\mu_Q\) is finite. By
  `positiveRationalQuotientHaarMeasure_isFiniteMeasure_iff`, \(\mu_Q\) is
  finite exactly when the Haar quotient measure on the norm-one rational
  quotient is finite. The latter is `connectedReductiveFiniteVolume`
  applied to the connected reductive group \(G\).

## Reduction to Hilbert–Schmidt operators

The proof applies
`groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution` to the
proved convolution identity `integratedActionConvolution`. This reduction
proves `GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement`. That
statement turns Hilbert–Schmidt operators \(R(f)\) for all adelic test
functions \(f\) into trace-class operators \(R(f)\) for all adelic test
functions. Its proof writes a test function as a finite sum of
convolutions \(\varphi_i \star \psi_i\) of test functions
(`IsAdelicTestFunction.exists_eq_sum_convolution`, the adelic
Dixmier–Malliavin factorization). Each
\(R(\varphi_i \star \psi_i) = R(\varphi_i) R(\psi_i)\) is a product of
two Hilbert–Schmidt operators and so is trace class. It then adds the
finitely many trace-class pieces. It remains to show that \(R(f)\) is
Hilbert–Schmidt for every adelic test function \(f\).

## Hilbert–Schmidt property for one test function

Fix an adelic test function \(f\) and put \(A = j \circ R(f)\), a bounded
operator from \(S\) to \(L^2(Q,\mu_Q)\). Apply the hypothesis to \(f\).
This gives \(C \ge 0\) and, by choice, a continuous representative
\(v_z\) of \(A z\) for every \(z \in S\) with \(|v_z(q)| \le C\|z\|\).

For \(q \in Q\), evaluation \(z \mapsto v_z(q)\) is complex-linear. Take
\(x, y \in S\) and \(c \in \mathbb C\). Then \(A(x+y) = Ax + Ay\) and
\(A(cx) = c\,Ax\) in \(L^2\). Together with the almost-everywhere equalities
\(Az = v_z\), they give
\(v_{x+y} = v_x + v_y\) and \(v_{cx} = c\,v_x\) \(\mu_Q\)-almost
everywhere. Both sides are continuous and \(\mu_Q\) is positive on open
sets. Therefore `Measure.eq_of_ae_eq` makes these equalities hold at every
point. The bound \(|v_z(q)| \le C\|z\|\) makes evaluation at \(q\) a
continuous linear functional \(k_q\) on \(S\) with \(\|k_q\| \le C\).

The family \((k_q)_{q \in Q}\) represents \(A\): for each \(z\),
\(Az = (q \mapsto k_q z)\) \(\mu_Q\)-almost everywhere. The theorem
`hilbertSchmidtUniformEvaluation` applies to \(A\), \(k\), \(C\) and the
finite measure \(\mu_Q\). Its first conclusion gives a Hilbert basis
\((b_i)\) of \(S\), indexed by a subset of \(S\), such that
\(\sum_i \|A b_i\|^2\) is summable. Since \(j\) is an isometry,
\(\|A b_i\| = \|R(f) b_i\|\). So the same basis shows that \(R(f)\) is
Hilbert–Schmidt in the sense of `IsHilbertSchmidt`. This holds for every
adelic test function. The reduction above then gives trace class.

## Source correspondence

The proof follows Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 9.3.3 and its proof, printed pp. 247–248
(one-based PDF pp. 259–260). The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
author errata `getz-hahn-2024-errata-2026-10` (October 2026), SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`, have
no entry for §9.3.

- The lemma's hypothesis \(\mathrm{meas}_{d_r g}([G]) < \infty\)
  corresponds to the finiteness of \(\mu_Q\) above. For reductive \(G\)
  the source obtains it from Theorem 2.6.3. Here it comes from
  `connectedReductiveFiniteVolume`.
- The closed invariant subspace \(V\) is the full cuspidal subspace \(S\).
  The estimate (9.13), \(\|R(f)\phi\|_\infty \ll_f \|\phi\|_2\), is the
  statement's hypothesis on continuous representatives.
- The source represents each evaluation functional by a Riesz vector
  \(K_{R(f),x}\). It bounds \(\|K_{R(f),x}\|_2\) uniformly in \(x\) and
  concludes from the resulting square-integrable kernel (Exercise 9.4).
  The proof here builds the same evaluation functionals \(k_q\) with the
  same uniform bound. It then uses `hilbertSchmidtUniformEvaluation`,
  which bounds finite Bessel sums over a Hilbert basis by an integral
  and builds no two-variable kernel.
- The source's last step uses the Dixmier–Malliavin lemma (Theorem 4.2.9,
  Exercise 9.8) and trace class of products of two Hilbert–Schmidt
  operators (Exercise 9.2). Here this step is
  `groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution`,
  instantiated with `integratedActionConvolution`.

The source takes test functions in
\(C_c^\infty(A_G\backslash G(\mathbb A_F))\). The statement uses the
Library's adelic test functions on the full adelic group and their
operators on the positive quotient; its Markdown explains this
formulation.
