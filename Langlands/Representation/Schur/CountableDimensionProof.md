# Proof of Schur's lemma in at most countable complex dimension

`Langlands.countableDimensionalSchur` proves the exact published proposition
`Langlands.CountableDimensionalSchurStatement` from
`Langlands.Representation.Schur.CountableDimensionStatement`.
It retains the independent universes `uG` and `uV` and all original hypotheses.
For every irreducible complex representation of algebraic dimension at most
`Cardinal.aleph0`, every equivariant endomorphism is a unique complex scalar
multiple of the identity.

Worker 66 implemented this proof. Worker 287 supplied the implementation
roadmap, including the commutative subfield reduction needed to apply
Mathlib's resolvent independence theorem.

## Implemented argument

The proof identifies equivariant endomorphisms with
`D = Module.End (MonoidAlgebra ℂ G) rho.asModule` using
`Representation.IntertwiningMap.equivAlgEnd`. Irreducibility makes
`rho.asModule` a simple, nontrivial module. Mathlib's
`Module.End.instDivisionRing` therefore equips `D` with a division ring
structure.

Choose a nonzero vector `v`. Evaluation at `v`, followed by
`rho.asModuleEquiv`, is a complex linear map `D →ₗ[ℂ] V`. It is injective:
if two endomorphisms agree at `v` but differ, their difference is a nonzero
endomorphism of a simple module, hence injective. Its vanishing at `v`
would force `v = 0`.

The private helper `countableDivisionAlgebra_algebraic` shows that every
element of a complex division algebra admitting such a linear injection
into a space of countable dimension is algebraic. For a purported
transcendental element `x`, it takes the subfield closure of `x` and the
complex scalars. In Mathlib a `Subfield` of a division ring need not be
commutative. Here the generators commute, and the private helper
`commute_subfield_closure` uses closure induction twice to extend this
commutation through addition, negation, multiplication, and inversion.
Thus this particular subfield carries a commutative field structure.
The complex scalar map restricts to it, and its inclusion in `D` is an
injective complex algebra homomorphism.

The lift of `x` to that field remains transcendental. Mathlib's
`Transcendental.linearIndependent_sub_inv` gives the linearly independent
family `(x - c)⁻¹`, indexed by all `c : ℂ`. The inclusion followed by
evaluation maps this to a linearly independent family in `V`.
`LinearIndependent.cardinal_lift_le_rank` bounds the lifted cardinality
of `ℂ` by the lifted rank of `V`, hence by `aleph0`. The cardinality of
`ℂ` is the continuum, strictly greater than `aleph0`, giving a
contradiction. Cardinal lifts preserve the arbitrary carrier universe.

Every element of `D` is consequently algebraic, hence integral over `ℂ`.
Since `ℂ` is algebraically closed and `D` is a domain,
`IsAlgClosed.algebraMap_bijective_of_isIntegral` says that the complex
scalar map into `D` is bijective. Transport through `equivAlgEnd` gives
scalar existence. Injectivity of the same scalar map gives uniqueness.
The intertwiner algebra map is precisely scalar multiplication of the
identity intertwiner.

## Provenance and scope

The source is I. N. Bernshtein and A. V. Zelevinskii, *Representations of
the group GL(n,F) where F is a non-Archimedean local field*, Russian
Mathematical Surveys 31:3 (1976), 1–68, English translation, Chapter I,
Proposition 2.11 and its proof, printed/PDF page 18. The irreducibility
conventions on printed/PDF page 15 were also checked.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- Source SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- [Original publication copy](https://www.math.tau.ac.il/~bernstei/Publication_list/publication_texts/B-Zel-RepsGL-Usp.pdf).

The published target extracts the algebraic portion of the source argument
and assumes the countable dimension bound directly. The source derives
that bound from smoothness and countability at infinity. This proof follows
the resolvent argument, using a commutative subfield and Mathlib's
partial-fractions theorem to implement linear independence. It then uses
algebraic closure to recover scalarity. These are internal proof steps,
not extra assumptions in the result.

Only the unchanged target module and Mathlib are imported. No topology,
smoothness, admissibility, finite-dimensionality, or countability condition
on `G` is introduced. The original statement and its imported files remain
unchanged; this module adds only the proof and its internal helpers.
