# Proof of the cycle and boundary criterion

`Langlands.Cohomology.ModuleComplex.natModuleQuasiIsoCriterion.{u}`
proves the unchanged internal proposition
`NatModuleQuasiIsoCriterionStatement.{u}`.

The proof uses Mathlib's actual short-complex homology. First, the
factorization of the map from cycles to opcycles through homology and
the injectivity of the homology inclusion show that two cycle classes
are equal precisely when their difference is a boundary. The quotient
description of opcycles in `ShortComplex.ModuleCat` supplies that last
equivalence.

For a morphism of short complexes, every homology class has a cycle
representative because the canonical projection from cycles is an
epimorphism of modules. Naturality of that projection and of the cycle
inclusion identifies the induced map with the map on representatives.
The injectivity test forces a class in its kernel to be zero, and the
surjectivity test supplies a representative of each target class. The
homology map is therefore bijective and hence an isomorphism.

Mathlib reduces a natural-number cochain complex to the corresponding
short complex in each degree. In degree zero the incoming differential
is zero, so the two degree-zero cycle tests give the short-complex
criterion. In every positive degree the hypotheses are already its
injectivity and surjectivity tests modulo boundaries. The resulting
isomorphisms on homology prove `QuasiIso`.

This is an internal algebraic adapter. It introduces no flatness or
boundedness assumption, no new quotient definition, and no geometric
sections comparison.
