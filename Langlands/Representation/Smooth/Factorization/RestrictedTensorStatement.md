# Admissibility and equivalence of restricted tensor representations

This pair states the representation-theoretic properties of the constructed
restricted tensor product in Flath's section 2, Example 2. Its entry declaration
is `Langlands.FlathRestrictedTensorStatement`, a conjunction of four closed
proposition definitions. No truth of these propositions is assumed or proved.

## Actual objects and hypotheses

The index type is arbitrary, with no countability requirement. Each local group
is a Hausdorff, locally compact, totally disconnected topological group, with a
specified compact open subgroup `H i`. The acting group is the actual cofinite
restricted product `Langlands.RestrictedTensor.RestrictedGroup G H`.
The local representations are algebraic complex representations on arbitrary
vector spaces, with no topology or finite-dimensionality imposed on the whole
space. The index, group, and two local-carrier universes are independent.

`ReferenceVectors V E` specifies nonzero vectors outside a finite exceptional
set `E`. The separately quantified `hr` says that each such vector is fixed by
the specified local subgroup. These are conditions on actual vectors and
operators, not assumptions of any admissibility or factorization theorem.

`Langlands.RestrictedTensor.productRepresentation` constructs the group action
on the actual algebraic direct limit of finite tensor products. Its action
and representation laws are already proved in the imported construction.
Reference vectors inside `E` are unnecessary: every finite stage contains
the entire exceptional set. Different choices of `E` are allowed in the
reference-independence and uniqueness clauses.

Every clause retains the one-dimensional-fixed-space condition at all but
finitely many indices:

```text
∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1
```

This is an assertion about the actual subgroup-fixed submodule. It is not a
free unramifiedness predicate or a condition on unspecified Hecke eigenvalues.
Its exceptional set need not equal the finite set used to supply reference
vectors. Proof work may enlarge to their union.

Admissibility uses the published `Langlands.IsAdmissible`: smoothness and
finite-dimensional fixed spaces for every open subgroup. This agrees with
the source's compact-open convention here. A compact open subgroup contained
in any open subgroup has a fixed space containing the latter's fixed space;
van Dantzig's theorem supplies such compact open subgroups. The restricted
product of the stated local groups relative to compact open subgroups is
again locally compact, Hausdorff and totally disconnected. These topological
facts are proof obligations when applying this bridge, not assumed
factorization data. Smoothness of the constructed action is already the
published `RestrictedTensor.isSmooth_productRepresentation`.

## Clauses

1. `RestrictedTensorAdmissibilityStatement` asserts admissibility of the
   constructed restricted tensor when every local factor is admissible and
   the almost-everywhere fixed spaces are one-dimensional.
2. `RestrictedTensorIrreducibilityStatement` asserts, under the same
   hypotheses, that the constructed representation is irreducible if and
   only if every local factor is irreducible.
3. `RestrictedTensorReferenceIndependenceStatement` asserts an equivariant
   linear isomorphism between the tensors formed using any two permitted
   choices of reference vectors and finite exceptional sets. It does not
   require local irreducibility.
4. `RestrictedTensorFactorUniquenessStatement` says that an equivariant
   linear isomorphism between two constructed tensors of admissible
   irreducible local factors implies an equivariant linear isomorphism
   between the two factors at every index. The two families of vector
   spaces have independent universes.

The conclusions use `Nonempty (Representation.Equiv ...)`, so they assert the
existence of genuine intertwining linear equivalences without requiring chosen
carrier types to be equal. Mathlib's `Representation.IsIrreducible` excludes
the zero representation. Zero exceptional factors are allowed in the first
three clauses; the resulting zero tensor is admissible, and its failure of
irreducibility agrees with the local criterion. All groups, instances, spaces,
operators, reference vectors and hypotheses are quantified inside each `Prop`.
The statements include finite and empty index types with the usual algebraic
tensor conventions.

## Original source and derived content

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-functions*, Proceedings of Symposia
in Pure Mathematics 33, Part 1 (1979), pp.179–183.

- Literature ID: `flath-1979-tensor-products`.
- Retained original:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
- SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- Primary locator: section 2, printed p.181, Example 2 and the preceding
  numbered assertion (3), one-based PDF p.177.
- Uniqueness context: Theorem 2 and its proof on the same page, and the final
  sentence of the proof of Theorem 1 on printed p.180, one-based PDF p.176.
- The entire article, printed pp.179–183, was read, including the different
  archimedean and Hilbert categories in sections 3–4.

The first three clauses translate Example 2. The source explicitly requires
admissible local representations and one-dimensional subgroup-fixed spaces
almost everywhere. It asserts independence of the choices of nonzero vectors
in those lines, admissibility, and the equivalence of global and local
irreducibility. Numbered assertion (3) explains the more general independence
under almost-everywhere changes within the same lines.

The fourth clause extracts the uniqueness conclusion for representations
already supplied as restricted tensors. Theorem 2 imposes commutativity of
the spherical Hecke algebras almost everywhere in order to obtain a
factorization of every admissible irreducible representation. This pair does
not assert that existence theorem. For already constructed tensors,
uniqueness follows by restriction to the single local group: separation of
that tensor factor writes the restriction as a nonzero direct sum of copies
of the local irreducible representation. Equivalent such restrictions have
equivalent local constituents. This is the isotypic-restriction argument
at the end of the proof of Theorem 1, applied to the constructed restricted
tensor. It does not require a spherical Hecke commutativity hypothesis.
This extraction is explicitly derived content, not a claim that the source
states Theorem 2 without its hypothesis.

The almost-everywhere fixed-line hypothesis is essential to the admissibility
claim in this group. It has not been replaced by the mere existence of a
nonzero fixed reference vector. Nor is any dimension bound on the entire
local representation assumed.

## Dependencies and remaining scope

The sole direct project import is
`Langlands.Representation.RestrictedTensor.Smooth`. It imports
`RestrictedTensor.Action`, `RestrictedTensor.Maps`, `RestrictedTensor.Basic`
and `Representation.Smooth.Definitions`. All five pairs are published in the
workspace's Library base
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

No pending `RestrictedTensor.Separation` module or two-factor statement is
imported to state this group. A future proof may use the published separation
construction once available. General factorization existence, the spherical
Hecke algebra hypothesis of Theorem 2, the archimedean `(g,K)` category of
Theorem 3, and the Hilbert completion of Theorem 4 remain separate obligations.
This group supplies prerequisites for local components; it does not define
cuspidal automorphic representations, Satake data, or the higher-rank
Jacquet–Shalika and Arthur–Clozel statements.

Worker 44 authored this pair over the published constructions. Compilation
and declaration inspection check well-formed propositions; independent
semantic review and publication are still required, and theorem proofs remain
separate work.
