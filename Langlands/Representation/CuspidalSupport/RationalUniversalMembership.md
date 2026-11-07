# Actual norm-kernel compact-induction block membership

This internal module fixes an affine group scheme locally of finite type over a
nonarchimedean local field, with connected reductivity, the canonical point
topology, and locally compact nonarchimedean rational points. The field universe
`uF` and original representation carrier universe `uV` are independent. Let `π`
be irreducible and assume compact smooth-dual coefficients for its entire
restriction to the complete common rational-character norm kernel.

`rationalNormKernelCompactInduction_mem_of_restriction` proves actual membership
of the published full-restriction compact induction in
`rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)`. Its other explicit
inputs are `RationalNormKernelFiniteRestrictionStatement.{uF,uV}` and
`RationalNormKernelTwistEquivalenceStatement.{uF,max uF uV,max uF uV}`. The finite
restriction statement supplies finitely many irreducible subrepresentations
spanning the whole restriction. The semisimplicity and finite-length conjuncts
are not used here.

For each irreducible actual subquotient `D` of the induction, the generic
`openNormalFamily_compactInduction_subquotient_restricted_hom` provides a nonzero
restricted intertwiner `D → π`. Compose this with the restriction of the actual
`SmoothRep.universeLiftEquiv` to obtain a restricted map into
`rationalInertiaBaseLift G π`. Injectivity of the lift equivalence proves this
composite is nonzero, and the lift preserves irreducibility. The second
biconditional of twist equivalence gives equivalence of the restrictions; the
first gives an unramified twist of `D` equivalent to the lifted base. Converting
this equivalence to a smooth isomorphism and applying inertia symmetry proves
that `D` lies in the lifted base's actual orbit. This covers every irreducible
actual subquotient, as required by the unchanged block property.

`rationalNormKernelCompactInductionBlockObject` bundles the actual compactly
induced function object with this proved membership. It changes neither its
carrier nor its action.

The argument is derived from published constructions and the generic
finite-family induction-support proof. It does not prove compactness of the
cuspidal restriction, finite restriction or twist equivalence from their original
hypotheses. Those structural results remain explicit inputs to this helper,
and the unchanged full small-progenerator target remains a separate obligation.
