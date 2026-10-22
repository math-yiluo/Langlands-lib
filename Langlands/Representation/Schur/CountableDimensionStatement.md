# Schur's lemma in at most countable complex dimension

`Langlands.CountableDimensionalSchurStatement` states that for any group `G`
and irreducible representation `rho : Representation ℂ G V` satisfying
`Module.rank ℂ V ≤ Cardinal.aleph0`, every equivariant endomorphism `f` has
the form `c • Representation.IntertwiningMap.id rho` for a unique `c : ℂ`.

The dimension is algebraic dimension over the complex numbers: the cardinality
of a Hamel basis. The bound includes finite dimension and countably infinite
dimension. It does not assert that the set of vectors is countable.
`Representation.IsIrreducible` is Mathlib's condition that the
subrepresentation lattice is a nontrivial simple order. It excludes the zero
representation and says that the only invariant subspaces are zero and the
whole space. The conclusion is equality of actual intertwining maps, so it
asserts scalar action on every vector. No choice of basis occurs in the
statement.

The group and vector-space universes `uG` and `uV` are independent.
No topology, smoothness, admissibility, or countability assumption on `G` is
required. The dimension bound is an explicit hypothesis, separate from
irreducibility. In particular this statement can be used after establishing
that bound for a smooth representation, without first proving admissibility.

## Source and derived formulation

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68, English translation, Chapter I, Proposition 2.11 and its proof,
printed/PDF page 18. The irreducibility and representation conventions on
page 15 were also checked.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- Source SHA256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- [Original publication copy](https://www.math.tau.ac.il/~bernstei/Publication_list/publication_texts/B-Zel-RepsGL-Usp.pdf).

This is a derived algebraic formulation of the argument in Proposition 2.11,
not a literal translation of its topological statement. The printed
proposition concerns an irreducible smooth representation of an l-group
countable at infinity. In its proof those topological hypotheses establish
that the representation has at most countable dimension: a nonzero vector
generates the representation, and its open stabilizer has countable index.
Here the dimension bound is supplied directly.

The remaining argument is algebraic. A nonzero equivariant endomorphism of
an irreducible representation is invertible. If an equivariant endomorphism
`A` were never scalar, every `A - c • id` would therefore be invertible.
For a fixed nonzero vector `v`, the vectors `(A - c • id)⁻¹ v`, indexed by
the complex numbers, are linearly independent: a finite dependence can be
multiplied by the denominators to obtain `P(A) v = 0` for a nonzero complex
polynomial `P`. Factoring `P` shows that `P(A)` is invertible, a
contradiction. The resulting uncountable independent family contradicts
the dimension bound. Uniqueness of the scalar is the additional immediate
consequence of evaluating two scalar operators on a nonzero vector.

These observations explain the formulation and its provenance. The Lean
file defines a proposition; it does not prove that proposition.

## Dependencies and scope

Only Mathlib is imported. `Mathlib.LinearAlgebra.Dimension.Basic` supplies
cardinal-valued module rank; `Mathlib.RepresentationTheory.Irreducible`
supplies the actual representation, irreducibility, and intertwiner types.
The complex scalar type comes from `Mathlib.Basic.Complex.Basic`.
Worker 189 authored this pair.

The existing project `Langlands.AdmissibleSchurStatement` and its proof use
admissibility to obtain a nonzero finite-dimensional fixed space. This target
has a different hypothesis and is independent of that proof. It states only
the scalar-endomorphism conclusion. Hom-space and central-character
consequences, and deductions of countable dimension from topological
hypotheses, are separate obligations.
