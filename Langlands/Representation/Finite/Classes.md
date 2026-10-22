# Finite-dimensional representation classes and trace characters

This construction uses Mathlib's actual `FDRep k G` category. `RepClass k G`
is its quotient by categorical isomorphism, using
`CategoryTheory.isIsomorphicSetoid`. Its equivalence relation is therefore the
existence of an equivariant linear isomorphism, not equality of characters.
`isoOfEquiv` and `equivOfIso` connect the existing category and unbundled
representation-equivalence interfaces.

The coefficient field is in universe `u`, the group is in an independent
universe `v`, and the underlying spaces of `FDRep` are in universe `u`.
Consequently the class quotient occupies the universe of the bundled category;
no smallness of that class space is asserted. `ofRepresentation` transports any
finite-dimensional representation from an arbitrary carrier universe to the
coordinate space `Fin (Module.finrank k V) → k`, using Mathlib's finite basis
and conjugation of endomorphisms. `modelEquiv` proves that this is an actual
equivariant linear equivalence. `classOfRepresentation_eq_iff` proves that
two models define the same class exactly when their original representations
are equivariantly equivalent, including independent source and target carrier
universes. Thus the carrier convention loses no finite-dimensional
representations. `classOfRepresentation_prod` proves that this class
constructor preserves direct sums.
`ComplexRepClass` specializes the field to the actual complex numbers.
These algebraic constructors work over every field and every group, so they
apply in particular to finite groups over characteristic-zero fields.

Direct sum is the product vector space with Mathlib's componentwise action.
The code proves its compatibility with isomorphisms and constructs equivariant
associativity, symmetry, and zero isomorphisms. Those isomorphisms establish
the additive commutative monoid laws on the quotient. The zero object is the
trivial action on the zero-dimensional space `Fin 0 → k`.
Tensor product uses Mathlib's monoidal structure on `FDRep`; restriction uses
the existing action restriction functor along a group homomorphism. Their
maps on isomorphism classes are justified by the corresponding maps on
isomorphisms. The tensor-product distributivity equivalence is the usual
`TensorProduct.prodRight` linear equivalence; its compatibility with the actions
is checked on pure tensors. This and the zero-dimensional tensor equivalence
construct the biadditive map `tensorHom`. Restriction is the additive map
`restrictHom`.

The dual is the contragredient: the action of `g` is precomposition by the
action of `g⁻¹`. Precomposition by the inverse of an equivariant isomorphism
establishes isomorphism congruence. The standard identification of the dual of
a product with the product of the duals establishes additivity of `dualHom`.
All of these constructor obligations are proved in Lean.

The character is the trace of the actual action. Mathlib's `FDRep.char_iso`
makes it well-defined on the quotient, and `LinearMap.trace_prodMap'` proves
the direct-sum additivity needed for `characterHom`. No injectivity of the
character map, irreducible basis, orthogonality, or spanning theorem is assumed.
The file also proves the tensor, contragredient, restriction, and conjugacy
formulas for these trace characters, reusing the corresponding pinned Mathlib
theorems where available.

## Original source and derived scope

Jean-Pierre Serre, *Linear Representations of Finite Groups*, English
translation by Leonard L. Scott, Springer GTM 42 (1977), Part I,
Section 1.1, printed pages 3-4 defines finite-dimensional complex
representations and their equivariant isomorphisms. Section 1.3, pages 5-7
describes direct sums, Section 1.5, pages 7-8 defines tensor products,
and Section 2.1, pages 10-11 defines the trace character and its direct-sum
and tensor-product formulas. Section 2.1, Exercise 2.3, printed page 12,
describes the contragredient and its character. These original passages were
read in the retained PDF. The coordinate-model construction and its intrinsic
equivalence proofs are internal finite-basis implementations, rather than
claims that the source specifies Lean universe conventions.

- Literature ID: `serre-1977-linear-representations`.
- Source SHA256:
  `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
- Retained source:
  `C:/Central-Library/Serre--Linear Representations of Finite Groups--1977.pdf`.

The quotient and bundled monoid are internal implementations of these
isomorphism and direct-sum conventions. Extending these algebraic definitions
from complex finite-group representations to arbitrary fields and groups
uses the explicit Mathlib constructions and the intrinsic proofs in this file;
it does not extend the source's semisimplicity or character-classification
theorems to those hypotheses.

## Dependencies and scope

There are no project mathematical imports. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.

The imported Mathlib modules are `RepresentationTheory.Character`,
`CategoryTheory.IsomorphismClasses`, `Analysis.Complex.Basic`,
`LinearAlgebra.Dual.Lemmas`, and `LinearAlgebra.TensorProduct.Prod`.
The construction does not assert cancellation, a representation-ring
identification, character faithfulness, or semisimplicity. Finite-index
induction, group completion, and the integral induced-character submodule are
subsequent construction groups within the assigned task. Independent semantic
review and current Library integration are required for acceptance.
