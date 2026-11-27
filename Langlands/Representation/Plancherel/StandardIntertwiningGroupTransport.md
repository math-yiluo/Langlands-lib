# Transport of standard integration between isomorphic ambient groups

`ambientEquivQuotient` uses `leftQuotientHomeomorph` for the quotient of the
target radical by its intersection with the source radical. It intertwines
the right translations, so pushing forward the given measure preserves
its right invariance.

`hasIntegral_ambientEquiv_iff` evaluates the actual standard integrands on
quotient representatives. The two integrands agree after precomposition
by the quotient homeomorphism. `hasIntegral_comp_continuousMulEquiv_iff`
identifies the smooth-dual tests and
`hasIntegral_measurePreserving_equiv_iff` transports the scalar integrals with
the specified measure. `domain_eq_top_ambientEquiv_iff` then uses the
induction equivalence and transports the representing functions by the
ambient isomorphism. These are derived steps for comparing prescribed
intertwiners when applying induction in stages.
