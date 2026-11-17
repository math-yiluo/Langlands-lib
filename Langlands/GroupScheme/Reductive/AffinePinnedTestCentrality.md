# Pinning rigidity on actual coefficient tests

This internal consequence extends the scalar rigidity of the supplied simple
vectors to every nontrivial coefficient algebra, using the actual smooth Lie
scalar-extension equivalence. Its chosen vectors project to the coefficient
extensions of the original supplied vectors. Injectivity of the actual kernel
base-change equivalence transfers scalar rigidity to those original vectors.

The predicate `TorusPermutesSimpleVectorsAt` expresses permutation by the actual
adjoint action on these coefficient extensions. The original all-test weight
equation forces each simple-root unit monomial to equal one, so the actual
simple-root character values equal one. Arbitrary-base root-annihilator
centrality gives the full centre condition on every further relative scheme
test. The coefficient ring may have nilpotents.

Derivation of the predicate from a pinning-preserving comparison and its inner
representative remains a separate obligation.
