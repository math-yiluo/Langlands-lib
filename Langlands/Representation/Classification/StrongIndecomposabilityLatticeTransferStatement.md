# Generic lattice transport for strong indecomposability

Authors: Worker 864 (initial statement draft) and Worker 185 (source check,
scope explanation and dependency audit).

This module defines one proposition,
`Langlands.Classification.StrongIndecomposabilityLatticeTransferStatement`.
It states two algebraic assertions about the published predicate
`Langlands.Classification.IsStronglyIndecomposable` and proves neither.
The content is internally derived from that predicate and elementary order
theory.

## The exact proposition

The declaration has five independent universes, in the order
`.{uK,uG,uH,uV,uW}`. It universally quantifies over a field `k : Type uK`,
groups `G : Type uG` and `H : Type uH`, additive commutative groups
`V : Type uV` and `W : Type uW` with `k`-module structures, and
representations `ρ : Representation k G V` and `σ : Representation k H W`.
Its conclusion is exactly the following conjunction:

1. For every supplied order isomorphism
   `e : Subrepresentation ρ ≃o Subrepresentation σ`,
   `IsStronglyIndecomposable ρ ↔ IsStronglyIndecomposable σ`.
2. For every actual `U : Subrepresentation ρ` with `U ≠ ⊥`, and every
   supplied order isomorphism
   `e : Subrepresentation σ ≃o Set.Iic U`,
   `IsStronglyIndecomposable ρ` is equivalent to
   `(∀ S : Subrepresentation ρ, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
   IsStronglyIndecomposable σ`.

`Subrepresentation ρ` is the actual lattice of invariant `k`-submodules of
`V`. Its bottom is the zero submodule, and its infimum is intersection of
the actual subspaces. The interval `Set.Iic U` consists of actual
subrepresentations `S` together with `S ≤ U`. It inherits the ambient order,
bottom and binary infimum; the bottom and infimum agree with the ambient
ones after taking subtype values.

The condition in the second clause says that `U` is essential in the
ambient representation: it meets every nonbottom ambient subrepresentation
nontrivially. It quantifies over every such ambient subrepresentation,
including those not contained in `U`. Both isomorphisms are supplied
isomorphisms of these actual ordered lattices. The proposition constructs
neither `U` nor an isomorphism. It neither assumes an isomorphism of
representations nor replaces subrepresentations with isomorphism classes.

The explicit `U ≠ ⊥` premise is necessary for the forward implication in
clause 2: a nonzero strongly indecomposable ambient representation does
not make its zero subrepresentation essential. Clause 1 includes zero
representations, on which the published intersection predicate is
vacuously true. There is no nontriviality, Artinianity, finite-length,
irreducibility, topology or smoothness hypothesis.

## Internal provenance and source motivation

The first assertion comes from the fact that an order isomorphism
preserves bottom and binary infimum. The second comes from the following
general lattice argument. For a specified nonbottom element `U`, the
nonzero-intersection property in the ambient lattice implies essentiality
of `U` and restricts to its lower interval. Conversely, essentiality makes
`U ⊓ S` and `U ⊓ T` nonbottom interval elements for any nonbottom ambient
`S` and `T`. Their meet lies below `S ⊓ T`, so the interval intersection
property gives the ambient intersection property. Transport along the
supplied order isomorphism identifies the interval condition with strong
indecomposability of `σ`. This explains the internally derived statement;
this module contains no implementation of that argument as a Lean proof.

The motivating original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), 165–210, §5.4, printed p.188 / one-based PDF
p.25, literature ID `zelevinsky-1980-induced-ii`, content SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
That page defines strong indecomposability by nonzero intersections. In
the proof of its Proposition, the submodule lattice of the actual highest
layer is compared with the highest derivative's lattice; the remaining
step uses intersection with every nonzero ambient submodule. This is the
motivation for the two clauses. The present arbitrary-field/group
formulation is an internal algebraic extension, not a literal analytic
theorem from that page.

The cited page was checked directly. A bounded filename search of the
current Library and project notes found no source-specific Zelevinsky
1980 errata note; this makes no general claim that no errata exist.
The zero-representation convention is inherited unchanged from the
published predicate and its explanation.

In the intended highest-layer application, construction of the actual
layer, its nonzeroness, its essentiality from homogeneity and its lattice
comparison with the actual derivative are separate analytic obligations.
No derivative, detection, exactness, filtration, plus-model, normalization,
homogeneity or product conclusion is a hypothesis or conclusion here.
This proposition gives no proof of mirabolic reduction, ordered-socle
existence or existence of an irreducible subrepresentation.

## Complete project import and declaration audit

The entire project import graph of this entry module is

```text
Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferStatement
  -> Langlands.Representation.Classification.StrongIndecomposability
     -> Langlands.Representation.SubrepresentationLattice
        -> Mathlib.RepresentationTheory.Intertwining
        -> Mathlib.Algebra.Module.Submodule.Map
```

There are no other project modules in the transitive closure.
`Mathlib.RepresentationTheory.Intertwining` imports Mathlib's
`RepresentationTheory.Subrepresentation`, which defines the actual
invariant-submodule type. The two imported project Lean/Markdown pairs
were read completely and are preserved unchanged.

The complete list of authored declarations in the project closure is:

| Module / namespace | Declarations and role |
| --- | --- |
| This entry module, `Langlands.Classification` | Only the Prop-valued definition `StrongIndecomposabilityLatticeTransferStatement`; no proof declaration. |
| `Classification.StrongIndecomposability`, `Langlands.Classification` | `IsStronglyIndecomposable` is exactly `∀ S T, S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥`. Its only theorem, `IsStronglyIndecomposable.of_subsingleton`, proves the vacuous zero-space case using `Subrepresentation.toSubmodule_injective` and subsingleton equality. The new definition uses the predicate, not that theorem. |
| `Representation.SubrepresentationLattice`, `Langlands.Subrepresentation` | `instSupSet`, `instInfSet`, `toSubmodule_sSup`, `toSubmodule_sInf`, `instCompleteLattice`, `toSubmodule_iSup`, `toSubmodule_iInf`, `mem_iInf`, `mapsTo_iSup`. These construct invariant submodule suprema/infima, identify their underlying submodules, characterize infimum membership and transport a supremum through an actual intertwiner. |

At the declaration level the new body uses the published intersection
predicate, actual representations and subrepresentations, order
isomorphisms, `Set.Iic` and the inherited order operations, alongside
logical connectives and the field/group/module structures. The complete
lattice in the lower project module is pulled back along Mathlib's
`Subrepresentation.toSubmodule_injective`. Its binary operations and
bottom reuse Mathlib's `Subrepresentation.instMin`,
`Subrepresentation.instLattice` and
`Subrepresentation.instBoundedOrder`. Mathlib's `coe_inf` is the literal
intersection identity, and the bottom's underlying submodule is `⊥`.
Thus the new statement uses the same bottom and intersection as the
unchanged predicate, rather than introducing a second interpretation.

The remaining lower declarations use only submodule lattice operations,
invariance under the actual action, and elementary maps and order
arguments. None imports or proves analytic, derivative, socle or
classification content. This accounts for the shared lower inputs as
well as the entry's direct predicate dependency; no excluded proof can
enter through an unexamined project import.

## Excluded downstream conclusions

The new statement is a lower algebraic input for ordered-socle existence
task `23189526-80b0-4828-a6d4-7ebec2cbeef5`. The audited closure excludes
that conclusion and every item below, including its proof successors and
transitive proof dependencies:

- Socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.
- Analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`.
- Segment-socle product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`.
- Final segment-socle irreducibility criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`.
- `AdjacentUnlinkedSegmentSocleSwap` and `TwoSegmentSocleCommutation`.
- Special-head product criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.
- Special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`.
- Ordered special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`.
- Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`.
- Tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- `SquareIntegrableLanglandsClassification` / `1cb45da2-7007-4351-a694-594fb148b8d1`.
- Square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`.
- Regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.
- `GenericSegmentProductUniqueness` / `30341ae4-65f2-4a0e-9283-763db01a409e`.
- Ordered special-segment conversion `8252833d-c269-41a9-824c-5879e531b23b`.
- Forward special-segment essential square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.

Only this statement pair belongs to this unit. A privately prepared proof
companion supplies no accepted input. An exact proof successor belongs to
a separate task after independent acceptance and publication of this
statement. The analytic detection, P1, recursion and product-homogeneity
work, and the separate finite-length work, remain outside its scope.
