# Proof of generic lattice transport for strong indecomposability

Authors: Worker 864 (Lean proof and initial explanation), Worker 185
(published target's dependency audit, adapted below), and Worker 695
(source, complete-interface and dependency verification, and final editing).

This module proves
`Langlands.Classification.StrongIndecomposabilityLatticeTransferStatement`
from the unchanged published statement module. The exact theorem is
`Langlands.Classification.strongIndecomposabilityLatticeTransfer`, with five
independent universe parameters `.{uK,uG,uH,uV,uW}` and no additional
hypotheses. Its type is that proposition itself.

## Target and helpers

The target universally quantifies over a field `k : Type uK`, groups
`G : Type uG` and `H : Type uH`, additive commutative groups
`V : Type uV` and `W : Type uW` with `k`-module structures, and actual
representations `ρ : Representation k G V` and `σ : Representation k H W`.
It asserts the conjunction of these two clauses:

1. Every supplied order isomorphism
   `e : Subrepresentation ρ ≃o Subrepresentation σ` gives
   `IsStronglyIndecomposable ρ ↔ IsStronglyIndecomposable σ`.
2. For every supplied actual `U : Subrepresentation ρ` with `U ≠ ⊥`,
   and every supplied `e : Subrepresentation σ ≃o Set.Iic U`,
   `IsStronglyIndecomposable ρ` is equivalent to
   `(∀ S : Subrepresentation ρ, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
   IsStronglyIndecomposable σ`.

`Subrepresentation` is the lattice of actual invariant submodules. Bottom
is zero and infimum is intersection. `Set.Iic U` contains the actual
subrepresentations contained in `U`, with their inclusion proofs. It
inherits the ambient order, bottom and infimum; taking subtype values
identifies its bottom and infimum with the ambient operations.
The essentiality clause quantifies over all nonbottom ambient `S`.
The proof constructs neither `U` nor the order isomorphisms. Clause 1
includes zero representations, where the intersection predicate is vacuous.
Clause 2 retains its explicit `U ≠ ⊥` hypothesis.

There are two public helpers in `Langlands.Classification`:
`stronglyIndecomposable_iff_of_orderIso` proves clause 1 for supplied `e`,
and `stronglyIndecomposable_iff_essential_interval` proves clause 2 for
supplied `U`, `hU` and `e`. They and the exact theorem are proved together
in this module.

## Implemented argument

The private lemma `nonbottom_inf_transport` works in two semilattices with
bottom. Suppose an order isomorphism `e` transports a pair of nonbottom
elements whose meet is bottom. Their preimages are nonbottom: otherwise
applying `e` and `e.map_bot` would make an original element bottom.
Applying `e.symm` to the bottom-meet equality, and rewriting with
`e.symm.map_inf` and `e.symm.map_bot`, contradicts the intersection
property of the preimages. Applying this lemma to `e` and `e.symm`
proves the first representation helper.

The private lemma `nonbottom_inf_essential_interval` works in a lattice
with bottom and a specified nonbottom `u`. In the forward direction the
ambient intersection property directly shows that `u` is essential.
It also restricts to `Set.Iic u`: subtype extensionality identifies a
bottom subtype with a bottom value, and taking subtype values turns a
bottom subtype intersection into a bottom ambient intersection.

Conversely, assume essentiality and the interval intersection property.
For nonbottom ambient `a` and `b`, define interval elements with values
`u ⊓ a` and `u ⊓ b`. Essentiality makes both nonbottom. If `a ⊓ b`
were bottom, `inf_le_inf inf_le_right inf_le_right` would put the meet
of those two values below bottom. `le_bot_iff` and subtype extensionality
would make the interval meet bottom, a contradiction. This proves the
ambient intersection property. No distributivity is required.

The second representation helper unfolds the published intersection
predicate, uses this essential-interval equivalence, and transports the
interval property along the supplied `e` and its inverse. Finally,
`strongIndecomposabilityLatticeTransfer` introduces the target's complete
telescope and pairs the two public helpers. No finiteness, nontriviality,
Artinianity, topology, smoothness or classification assumption is added.

## Provenance

This proof is an internal order-theoretic derivation from the published
intersection predicate. Its motivation is the algebraic step in
A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
165–210, §5.4, printed p.188 / one-based PDF p.25. The registered source
is `zelevinsky-1980-induced-ii`, content SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
That passage motivates comparison of the actual highest layer's lattice
with the highest derivative's lattice, together with intersection of
the highest layer with every nonzero ambient submodule. The arbitrary
field/group theorem proved here is an internal extension of that
algebraic argument, rather than a literal analytic assertion in the paper.

The cited original page was read directly and visually checked; its file
fingerprint matches the registered source. A bounded filename search of the
current Library and public project notes found no source-specific Zelevinsky
1980 errata note. This is not a claim that no errata exist.

Construction of the actual highest layer, its nonzeroness, its lattice
comparison with a derivative and essentiality from homogeneity are
separate analytic obligations. This module proves no derivative,
filtration, plus-model, detection, exactness, homogeneity, normalized
induction or ordered-socle conclusion.

## Complete project dependency audit

The only direct project import is the published target. The full project
import graph, including this entry module, is:

```text
Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof
  -> Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferStatement
     -> Langlands.Representation.Classification.StrongIndecomposability
        -> Langlands.Representation.SubrepresentationLattice
           -> Mathlib.RepresentationTheory.Intertwining
           -> Mathlib.Algebra.Module.Submodule.Map
```

The imported three project Lean/Markdown pairs are preserved unchanged.
Their entire authored declaration inventory, together with this proof,
is recorded here:

| Module | Declarations and role |
| --- | --- |
| This proof, namespace `Langlands.Classification` | Private `nonbottom_inf_transport` and `nonbottom_inf_essential_interval`; public `stronglyIndecomposable_iff_of_orderIso`, `stronglyIndecomposable_iff_essential_interval`, and exact `strongIndecomposabilityLatticeTransfer`. Their arguments are described above. |
| `Classification.StrongIndecomposabilityLatticeTransferStatement` | Only `Langlands.Classification.StrongIndecomposabilityLatticeTransferStatement`, the Prop-valued conjunction proved here. |
| `Classification.StrongIndecomposability` | `Langlands.Classification.IsStronglyIndecomposable`, the actual nonbottom-intersection predicate, and `IsStronglyIndecomposable.of_subsingleton`, its vacuous zero-space consequence. The proof uses the predicate, not that theorem. |
| `Representation.SubrepresentationLattice` | In `Langlands.Subrepresentation`: `instSupSet`, `instInfSet`, `toSubmodule_sSup`, `toSubmodule_sInf`, `instCompleteLattice`, `toSubmodule_iSup`, `toSubmodule_iInf`, `mem_iInf`, `mapsTo_iSup`. These construct and describe invariant submodule lattice operations and an intertwiner's action on a supremum. |

The target and proof use Mathlib's actual invariant-submodule type and
order. The lower complete lattice is pulled back along
`Subrepresentation.toSubmodule_injective`; its bottom and binary meet
reuse Mathlib's existing bounded order and lattice. The proof's
Mathlib dependencies are elementary order-isomorphism identities,
subtype extensionality and lattice inequalities, with the interval
order structure. None of the lower project declarations imports or
proves an analytic, derivative, socle or classification conclusion.
Thus no excluded conclusion can enter through an unexamined project
import or theorem dependency.

## Inherited exclusions

This is a lower algebraic input to ordered-socle existence task 23189526-80b0-4828-a6d4-7ebec2cbeef5. Exclude that conclusion and socle exhaustion f3a69bc8-7312-4f82-8a7d-ea3c8188cb63, analytic segment classification aca8805b-054f-4d56-8045-12db7f623404, segment-socle product irreducibility 23e98d90-6055-4e35-91a9-b0f5d8a84961, final segment-socle irreducibility criterion 2ae5cbe5-0701-4509-88a0-db8cbeb35be4, AdjacentUnlinkedSegmentSocleSwap, TwoSegmentSocleCommutation, special-head product criterion 8364e73f-14ec-4d14-8f2b-1555a7c1ce95, special-head exhaustion 3bfb61fa-1129-4fc9-83fd-7fcfec22106e, ordered special-head existence ebea9a8a-9b21-4208-aa31-98c2dea1f8a3, quotient coverage 20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584, tempered block uniqueness 52e97845-36bb-457d-b76f-70753334b88c, SquareIntegrableLanglandsClassification / 1cb45da2-7007-4351-a694-594fb148b8d1, square-integrable exhaustion cd8ab97c-0b78-4bce-97c4-d307a28159a4, regular exhaustion bf433f0a-921a-428c-b0c0-6475438125ac, GenericSegmentProductUniqueness / 30341ae4-65f2-4a0e-9283-763db01a409e, ordered special-segment conversion 8252833d-c269-41a9-824c-5879e531b23b, and forward special-segment essential square-integrability 5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807. These exclusions cover the mathematical conclusions, their proof successors and transitive proof dependencies. The shared lower inputs are accounted for in the complete import and declaration audit above; none contains an excluded conclusion. No lower split is introduced.

The inherited operator decision also excludes `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5`, and the segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292`, including their proof successors and transitive proof dependencies. No derivative input is needed in this generic lattice proof. In the separate analytic application the allowed derivative route is proved, independently accepted Bernstein-Zelevinsky 1977 general theory; Zelevinsky 1980 segment derivative formulas 3.5 and 9.6 remain excluded. Operator pauses on other tasks remain in force, including minus exactness `b65bc667-6951-4bd5-82af-10fb7046df7f`; this proof neither resumes nor bypasses them.
