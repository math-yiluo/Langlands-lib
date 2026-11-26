# Constant terms of locally bounded functions on a rational parabolic quotient

For a standard parabolic `P` of a connected reductive group over a number field,
`hasConstantTerm_of_locallyBoundedInvariant` proves convergence of the integral used in
`ArthurTruncation.constantTerm`. The rational points of the unipotent radical belong to `P(F)`,
so left `P(F)`-invariance makes `n ↦ φ(nx)` descend measurably to the rational radical quotient.
That quotient is compact and its normalized Haar measure has mass one. A compact set of
representatives in the radical gives a bound on the descended function by the local bound for
`φ` on its right translate by `x`. A measurable bounded function on this probability space is
integrable. [Compact radical quotient](AdelicStandardConstantTermIntegral.md)

`constantTerm_rationalParabolic_mul` proves that the radical average is left `P(F)`-invariant.
Conjugation by a rational parabolic point preserves the radical and its rational subgroup. The
induced isomorphism on the compact rational quotient preserves the normalized Haar measure.
Applying change of variables reduces the equality to left invariance of `φ` and uses the same
integrand at every representative of a coset. This is the change of variables used to regroup
Arthur’s (13.10) by `Q(F) \ P(F)`. [Measure transport](AdelicSubgroupQuotientTransport.md)

## Source

J. Arthur, *An introduction to the trace formula* (2005), §13, the definition of partial truncation
and the proof of (13.10), printed pp. 73–74, PDF pp. 85–86. Literature ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
