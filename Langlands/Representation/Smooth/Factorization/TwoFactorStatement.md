# Two-factor decomposition of admissible representations

This pair formulates the two-group tensor-factorization prerequisite used in
the construction and uniqueness of nonarchimedean local components. Its entry
declaration is `Langlands.FlathTwoFactorStatement`. It is a conjunction of four
proposition definitions; no truth of these propositions is assumed or proved.

## Actual objects and clauses

The coefficient field is the complex numbers. The groups in the representation
theorems are Hausdorff, locally compact, totally disconnected topological groups,
with no countability assumption. The representation spaces are arbitrary
algebraic complex vector spaces, with no topology and no assumption that their
whole dimension is finite.

For representations `ρ₁` of `G₁` and `ρ₂` of `G₂`, the external tensor in the
code is the actual Mathlib representation
`Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂)) (ρ₂.comp (MonoidHom.snd G₁ G₂))`.
Thus `(g₁,g₂)` acts on `v₁ ⊗ v₂` by `ρ₁(g₁)v₁ ⊗ ρ₂(g₂)v₂`. This uses
constructed projection homomorphisms, pullback, and the algebraic tensor
product. It is not a supplied representation with an assumed tensor property.

The component declarations are:

1. `ProductFixedVectorsStatement` identifies the image of the canonical map
   `V₁^K₁ ⊗ V₂^K₂ → V₁ ⊗ V₂` with the fixed subspace for `K₁ × K₂`, and
   asserts injectivity of that map. The map is the tensor of the actual
   subspace inclusions. This clause is formulated for arbitrary subgroups of
   arbitrary groups; it needs neither topology nor smoothness.
2. `AdmissibleExternalTensorStatement` asserts that an external tensor of
   admissible representations is admissible, and that it is irreducible if
   both factors are irreducible.
3. `AdmissibleProductFactorizationStatement` asserts the existence of two
   admissible irreducible factors for every admissible irreducible
   representation of `G₁ × G₂`, together with a genuine equivariant linear
   isomorphism from the given representation to their external tensor.
4. `AdmissibleProductFactorUniquenessStatement` states that an equivariant
   isomorphism between two such tensors forces equivariant isomorphisms
   between their respective factors. The four factor spaces can live in
   different universes; no equality of carrier types or selected bases is
   required.

All groups, instances, spaces and representations are quantified inside each
proposition. The two group universes, the four factor-space universes, and the
universe of the given product representation are independent. In the existence
clause, `ModuleCat.{uV} ℂ` packages a carrier of the same universe as the given
space, its additive group, and its scalar action. It supplies no representation
or theorem. Factors may be realized by subspaces of the given representation
after choosing a nonzero vector in the complementary factor; the statement
therefore does not need to enlarge the carrier universe. The representation
and isomorphism themselves remain existential conclusions.

Irreducibility is Mathlib's `Representation.IsIrreducible`, which excludes the
zero representation. Admissibility is the published `Langlands.IsAdmissible`:
smoothness and finite-dimensional fixed spaces for every open subgroup. For
the groups at issue this agrees with the compact-open convention in the source.
Indeed, van Dantzig's theorem supplies a compact open subgroup inside any open
subgroup; its finite-dimensional fixed space contains the fixed space of the
larger subgroup. The reverse implication is immediate. Product compact open
subgroups form an identity-neighborhood basis in the product group. These
standard bridges are part of the future proof work, not extra hypotheses or
assumed fields.

## Original source and translation

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-functions*, Proceedings of Symposia
in Pure Mathematics 33, Part 1 (1979), pp.179–183.

- Literature ID: `flath-1979-tensor-products`.
- Retained original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
- SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- Main locator: Theorem 1, clauses (1.1)–(1.2), printed p.179, and its complete
  proof, printed p.180; one-based PDF pages 175–176.
- The fixed-vector formula is item (iii) at the start of that proof.
- Section 2, printed pp.180–181, and Sections 3–4, pp.181–182, distinguish the
  restricted-tensor, archimedean, and Hilbert versions. The whole pp.179–183
  was read to preserve these boundaries.

The factorization and uniqueness assertions translate Theorem 1 directly,
with actual representations and equivariant linear equivalences. The source
works over the complex numbers and uses the ordinary convention that locally
compact groups are Hausdorff; the Lean hypotheses make the latter explicit.
No unitarity, global field, reductivity, or local Langlands correspondence
is assumed. The tensor-admissibility clause separates out the admissibility
consequence used in the source's proof before imposing irreducibility.

The fixed-vector clause strengthens the compact-open smooth case of item
(iii) to arbitrary subgroups, and specifies the canonical map. This is
derived algebraic content: a tensor is a finite sum, so linear independence
of the second-factor coefficients detects invariance of the first-factor
coefficients, and then independence in the first factor detects invariance
in the second. Inclusions of vector spaces remain injective under tensoring
over a field. Thus no averaging, finite group order, or Haar measure hypothesis
is needed for this clause. These explanations record the provenance of the
target; they do not insert a Lean proof.

## Dependencies and remaining scope

The only project import is the currently published
`Langlands.Representation.Smooth.Definitions`, inspected in Library
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The source pair is unchanged from
its published version 1: Lean SHA256
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`,
Markdown SHA256
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
Mathlib supplies `Representation`,
`Representation.tprod`, `Representation.Equiv`, `Representation.IsIrreducible`,
`TensorProduct.map`, `ModuleCat`, and the actual topological-group classes.
The environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

This finite-product prerequisite does not assert Flath's infinite-product
Theorem 2, which requires spherical Hecke-algebra commutativity almost
everywhere, or his number-field Theorem 3, whose archimedean factors are
admissible `(g,K)`-modules. The Hilbert tensor completion of Theorem 4 is
also outside this pair. Worker 58 retains the separate restricted-tensor
constructions, and Worker 2 retains actual global automorphic realizations,
local-component assembly, and spherical Hecke/Satake definitions. The
general Jacquet–Shalika and Arthur–Clozel target families remain outstanding.

Worker 44 authored this statement pair. Compilation and inspection establish
well-formed propositions only; independent semantic review and publication
are required, and mathematical proofs remain separate obligations.
