# Renard's Noetherian-object criteria

This statement unit compares the published source-facing Noetherian-object definition with three conditions on actual categorical subobjects. It states the equivalences and proves none of them. The imported `Langlands.CategoryTheory.RenardFiniteType` pair is unchanged.

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The retained file is `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. The original PDF254–255 was read in full through `resource_pdf`, and both original page images were visually checked during this unit's preparation. The primary definition and both source characterizations occur in A.I.3, printed248/PDF254, immediately after the categorical subobject order in A.I.2. The following finite-type discussion continues onto printed249/PDF255.

The published definition companion and `notes/renard/appendix-a-corrections.md` were consulted. No dedicated Renard 2026 errata file was found in the project or published notes. The registered supplementary source `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, is retained at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`. Its PDF18–19 extracts were reread. Those pages do not address the wording repairs below. This is a limited errata check, with no author-issued correction claimed.

## Actual constructions and scope

Every declaration is a transparent `def` returning `Prop` in namespace `Langlands.Renard`. Its complete parameter telescope is

```lean
(C : Type u) [Category.{v} C]
```

The object and Hom universes are independent. All remaining inputs are bound inside the proposition.

`CategoryTheory.Subobject X` is the existing quotient of monomorphisms into `X` by isomorphism over `X`. Its existing partial order is factorization of the inclusion arrows. Every subset, chain, comparison and equality below uses that actual type and order. No small representative type or replacement order is chosen.

The imported `Langlands.Renard.IsNoetherianObject X` means

```lean
∀ S : Set (Subobject X), S.Nonempty →
  ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q = P
```

The chosen element belongs to the subset and is maximal there. It need not be greater than every element of an arbitrary subset. This definition does not require any union to exist.

There are no hypotheses about abelian structure, zero objects, subobject unions, well-poweredness, smallness, complete lattices, Grothendieck conditions, modules, dimension or finite type. The subobject type may be large at the given universes. The separate all-unions context in Renard's following finite-type paragraph is not imposed on these Noetherian criteria.

## Exact statement family

`NoetherianMathlibComparisonStatement C` is

```lean
∀ X : C,
  Langlands.Renard.IsNoetherianObject X ↔
    CategoryTheory.IsNoetherianObject X
```

Mathlib's right-hand object predicate is defined from `WellFoundedGT (Subobject X)`. It occurs as the right side of this equivalence, not as an assumed instance. This is an internal source-to-Library comparison; Renard does not print a theorem referring to Mathlib.

`NoetherianChainMaximalityStatement C` is

```lean
∀ X : C,
  Langlands.Renard.IsNoetherianObject X ↔
    ∀ S : Set (Subobject X), S.Nonempty → IsChain (· ≤ ·) S →
      ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q = P
```

A chain is a subset totally ordered by the existing subobject order. Its nonemptiness is explicit. Within a chain, a maximal member is also greatest, but the formula uses the same maximality condition as the source definition. It asserts existence of a member, not merely existence of an upper bound outside the chain.

`NoetherianSequenceStabilizationStatement C` is

```lean
∀ X : C,
  Langlands.Renard.IsNoetherianObject X ↔
    ∀ f : ℕ → Subobject X, Monotone f →
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m
```

This quantifies over every increasing sequence, including constant sequences. A single index works for every subsequent index. No equality between just one pair of values, strict-monotonicity hypothesis, or union of the sequence replaces eventual stabilization.

`NoetherianCriteriaStatement C` is exactly

```lean
NoetherianMathlibComparisonStatement C ∧
  NoetherianChainMaximalityStatement C ∧
    NoetherianSequenceStabilizationStatement C
```

The conjunction is associated to the right. Each component and the aggregate retain exactly the category and its category instance as external parameters.

## Source wording and provenance

The first A.I.3 paragraph defines Noetherianity by maximal elements of nonempty subsets, gives the chain characterization, and says that increasing sequences suffice in practice. The chain and sequence statement components specify those assertions precisely. Renard cites [25], Proposition 1.6.1, for the chain discussion. That bibliographic source was not read for this unit and provides no proof evidence here.

The imported companion documents two repairs relevant to this unit. After selecting a subobject in a subset, the printed text calls the ambient object maximal; the maximal element must instead be the selected subobject. The printed unrestricted chain wording must also exclude the empty chain, which has no maximal element, even when the object is zero and its subobject order is a singleton. The chain statement makes this nonemptiness explicit. These are internal mathematical diagnoses based on the original, not attributed to an author-issued erratum.

Mathlib at the prepared commit supplies `CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`, with order homomorphisms from naturals, and general well-founded-order results such as `wellFounded_iff_has_min` and `wellFoundedGT_iff_monotone_chain_condition`. They suggest routes for a later proof. They are neither assumptions of the present propositions nor proofs of this exact source-facing aggregate.

## Remaining proof obligations

Worker 695 reused Worker 6's complete shared draft for these four declarations and their companion, independently checking the cited original passages, existing definitions and Mathlib interface. Both workers contributed to this statement unit.

A separate proof successor must target the exact published `NoetherianCriteriaStatement` after independent statement acceptance and publication. Development compilation and full declaration diagnostics do not prove the equivalences.

The general finite-type/finite-subcover comparison, the all-subobjects-finite-type characterization, the source Noetherian-category convention, actual ModuleCat examples and the Noether-isomorphism family are separate obligations. No theorem in any of those families is supplied or assumed by this unit.
