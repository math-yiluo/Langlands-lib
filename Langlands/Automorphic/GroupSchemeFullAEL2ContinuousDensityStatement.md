# Dense continuous cuspidal classes in closed invariant subspaces

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2ContinuousDensityStatement`
concerns an affine locally finite-type connected reductive group over a number
field. It uses a split central torus with injective, finite-index character
restriction, a supplied `ParabolicDynamicStatement`, and right invariance of
Haar measure on the norm-one group. Its space \(S\) is the existing full
almost-everywhere cuspidal subspace of the measured positive rational
quotient. The action on \(S\) is the original adelic right action.

For each closed invariant complex subspace \(P\) of \(S\), the vectors of
\(P\) represented by continuous cuspidal functions are dense in the norm
topology of \(P\). The classes in the dense set are exactly those in the
range of `positiveParabolicCuspidalL2ToFullAE` that lie in \(P\). That map
takes actual square-integrable continuous functions to their \(L^2\)
classes. Its source imposes pointwise vanishing of the constant terms
for every proper rational parabolic, with the existing mass-one measures
on the unipotent rational quotients.

This is a derived step toward the comparison of cuspidal functions and
cuspidal Hilbert vectors. Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), use strong convergence along Dirac sequences in
§9.3, printed p. 246 (PDF p. 258), and continuous evaluations of
convolutions in Lemma 9.3.3 and (9.13), printed pp. 247–248 (PDF
pp. 259–260). The Library's continuous representative estimate and
strong approximation apply to the same original quotient action. The
equivalence for continuous representatives in
`groupSchemeFullAEL2ContinuousCuspidality` then gives pointwise vanishing
on all adelic translates, as in the cuspidal period argument of §9.2,
printed pp. 242–245 (PDF pp. 254–257). Closed invariance keeps the
convolutions in \(P\).

The density here concerns continuous functions. The algebraic and Hilbert
comparison in Getz–Hahn Theorem 9.7.3 also involves finite-vector and
growth conditions. The source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
