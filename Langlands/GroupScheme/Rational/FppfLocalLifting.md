# Finite local lifting for ordered products

This internal module supplies the local lifting step needed in the final
central-extension argument for ordered products. It works over any base scheme
and at an arbitrary universe. It proves no semigroup realization or full
ordered-product theorem.

`FppfLiftFamily` is the data of one such simultaneous lift: a scheme over the
base, an fppf morphism to the original test scheme, a lifted point for each
factor, and the commuting equations. Here fppf means flat, surjective and
locally of finite presentation. The structure records the cover and all lifts
together; it imposes no bound on the base universe.

`exists_fppf_lift_family` says that a finite family of points lifts simultaneously
along flat surjective morphisms locally of finite presentation after an fppf
change of the test scheme. Its proof inducts on the size of the family. Each
successor step pulls back the first morphism and lifts the remaining points over
that pullback; the composite cover is again fppf. For the empty family the cover
is the identity. No pointwise surjectivity on the original test scheme is assumed.
`nonempty_fppfLiftFamily` packages that existence result as nonemptiness of the
defined lift structure.

`isIso_of_effectiveEpi_factorization` says that a monomorphism of schemes over
the base is an isomorphism when an effective epimorphism onto its target factors
through it. The proof uses Mathlib's strong epimorphism cancellation theorem and
the fact that a strong epimorphism which is a monomorphism is an isomorphism.
Flat surjections locally of finite presentation are effective epimorphisms by
Mathlib's fppf descent theorem. The lemma also applies to other effective covers.

These are internal consequences of Mathlib's pullback, morphism-property and
effective-epimorphism APIs. Their intended application is the final local-lifting
step in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Theorem 3.3.11, printed pp.115–116 (PDF pp.141–142), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The Lean proof uses strong
epimorphisms to express the descent step.
