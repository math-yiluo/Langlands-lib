# Cartan symmetric algebras and compact conjugation

Author: Worker 94.

This internal prerequisite extends the published matrix Cartan decomposition
and actual adjoint conjugation using Mathlib scalar extension and the universal
property of its symmetric algebra. Its provenance is this construction from
`ArchimedeanRelativeAdjoint` and `ArchimedeanCompactLieAlgebra`; it does not
attribute a new theorem to external literature. All constructions work for an
arbitrary field `K : Type u` and natural rank `n`. The Noetherian conclusion
additionally assumes `NumberField K`. There is no restriction on the universe
or on rank zero.

`ComplexCartanComplement` is the complex scalar extension of the actual
self-adjoint real submodule. `cartanComplexInclusion` and
`cartanComplexProjection` extend the published inclusion and complementary
projection. Projection after inclusion is the identity: the proof reduces to
pure tensors and uses the real self-adjoint projection formula
`(X + star X) / 2`. Hence the complex inclusion is injective.

The published `realLieConjugation_star` shows that conjugation by every element
of the standard infinite compact subgroup preserves self-adjoint matrices.
`cartanRealConjugation` restricts that conjugation to the real complement, and
`cartanComplexConjugation` extends it to complex scalars. Their identity,
composition and inverse laws are proved from the corresponding actual adjoint
laws. The inclusion and projection commute with these maps. For the real
projection this follows by conjugating its displayed formula; the complex
identities follow on pure tensors. These are actions of the full compact
subgroup, including its disconnected components.

`LieSymmetricAlgebra` and `CartanSymmetricAlgebra` are Mathlib symmetric
algebras on the actual full complexified Lie algebra and complementary space.
`cartanSymmetricInclusion` and `cartanSymmetricProjection` are universal lifts
of the corresponding complex linear maps. Checking generators proves that
projection after inclusion is the identity. Thus the inclusion is injective
and the projection is surjective.

`lieSymmetricConjugation` extends actual full-group adjoint conjugation to the
first symmetric algebra. `cartanSymmetricConjugation` extends compact
conjugation to the second. They are complex algebra automorphisms. A private
helper constructs these automorphisms by lifting each linear equivalence and
its inverse; their inverse identities are checked on generators. The public
identity, composition and inverse laws follow on generators as well. Finally,
`cartanSymmetricInclusion_conjugation` and
`cartanSymmetricProjection_conjugation` prove equivariance for every element
of the full standard compact subgroup, again by checking generators.

For a number field, the real matrix Lie algebra is finite dimensional through
its published linear equivalence with the actual matrix space. The real
submodule and its complex scalar extension are therefore finite dimensional.
A finite complex basis identifies the complementary symmetric algebra with a
polynomial algebra in finitely many variables. Transporting the Hilbert basis
theorem across this equivalence proves
`cartanSymmetricAlgebra_isNoetherianRing`.

These are symmetric algebras on vectors. A comparison with polynomial functions
on the original spaces through trace duality remains a separate construction.
This module supplies no invariant projection, continuity theorem, PBW
comparison, invariant restriction finiteness, covariant finite generation,
central covering, admissibility or automorphic growth theorem.
