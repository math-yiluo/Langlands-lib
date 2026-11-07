# Faithful integer Hom for the actual norm-kernel compact induction

This internal construction uses the actual compact induction of the entire
restriction to the complete rational-norm kernel, based at an arbitrary smooth
complex representation. The field and original carrier universes remain
independent; the block and the compact-induction carrier have universe
`max uF uV`, and the block base is the published `rationalInertiaBaseLift`.

Every irreducible object in that base's actual unramified orbit is a quotient
of the compact induction by `RationalUniversalQuotients`. Such a quotient map
is nonzero: irreducibility gives a nonzero vector in its target, and surjectivity
gives a preimage. For each irreducible subquotient of an object of the block,
the defining block property supplies exactly that orbit relation.

Assume explicitly that the induction belongs to this block and that the whole
norm-kernel restriction has compact smooth-dual coefficients. The latter
hypothesis gives ambient projectivity by `RationalUniversalProjectivity`.
The general `Category.ProjectiveGeneration` criterion then proves that the
actual integer-module-valued `preadditiveCoyonedaInt` of this block object is
faithful. Its proof detects a nonzero difference of morphisms by lifting through
an irreducible subquotient of the actual image. The definition
`rationalNormKernelBlockDetector` chooses such a detecting block morphism, and
its companion theorem proves that its composite with the given map is nonzero.

This result is derived from the imported constructions and criteria. It requires
no abelian structure on the block, finite length, admissibility or irreducibility
of the original base. The membership and compact-restriction hypotheses are
explicit unresolved inputs here; this module does not prove the full
`RationalUniversalSmallProgeneratorStatement` or add premises to that target.
