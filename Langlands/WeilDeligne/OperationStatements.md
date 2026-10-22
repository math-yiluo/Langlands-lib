# Weil–Deligne operation and correction statements

Worker 1 authored this proposition-definition family for task
`4bcfd048-60a1-4be4-a737-2fb8c48efc46`, using Worker 17's operation
constructors. Its whole target is
`Langlands.WeilDeligneRepresentation.OperationLaws.Statement`.
These are theorem statements, not their proofs. Compilation and declaration
inspection do not establish mathematical acceptance.

## Actual objects and assumptions

The file imports the companion's actual finite-dimensional complex
Weil–Deligne pairs, sum, tensor, negative-transpose dual, character twist,
and monodromy-kernel representation. Their nilpotence and covariance
certificates remain those of the constructors. The statements do not
substitute a new pair structure, use classification, or choose a correction.
All ranks, including zero, and independently universed carriers are allowed.

The correction predicates and semisimplification relation are precisely
those of `FrobeniusStatements`. A supplied correction is an actual unipotent
linear automorphism commuting with the action and monodromy, with the
specified semisimplicity conditions. The corrected action uses the
negative integer degree. Existence of such a correction is a separate
target in that file, with surjective degree, finite inertia image, and
the norm `q` to the negative degree for `q > 1`.

The preservation implications in this file need no additional existence
or classification hypotheses: they start with explicit correction or
semisimplification witnesses. They therefore apply in particular under
the exact assumptions of that existence theorem. Neither Frobenius
semisimplicity nor the operations impose zero monodromy.

## Declaration-level source and dependency map

All declarations in the table are in the namespace
`Langlands.WeilDeligneRepresentation.OperationLaws`.

| Declaration | Meaning and precise provenance |
| --- | --- |
| `Formulas` | Componentwise sum, diagonal tensor action, tensor monodromy `N tensor 1 + 1 tensor N'`, inverse-element dual action with minus transpose monodromy, and scalar twist with unchanged `N`. Tate 4.1.2 and 4.1.5; the dual sign is the infinitesimal dual of the additive action in Tate 4.1.1–4.1.2. Uses the actual companion constructors. |
| `MapFormulas`, `FunctorLaws` | Actual product and tensor maps, transpose in the reverse direction, and unchanged twist maps. Identities and composition are stated with contravariant dual order. Direct linear-algebra consequences of Tate 4.1.2 and its definition of morphism, using the companion's `Hom`, `sumMap`, `tensorMap`, `dualMap`, and `twistMap`. |
| `IsomorphismCompatibility` | These operations preserve genuine invertible intertwiners commuting with `N`, including distinct carrier universes. Derived from the same explicit maps, not from dimensions or block classification. |
| `ZeroMonodromyCompatibility` | Zero-monodromy embedding commutes with all four operations through identity carrier identifications. Directly derived from their formulas and the companion's `zeroMonodromy`. |
| `DualCompatibility` | Dual of a sum, tensor of duals to dual of tensor, and evaluation into the bidual, all as actual WD equivalences with explicit evaluation formulas. Henniart2002 2.1 states the first isomorphism. The other two are finite-dimensional linear duality applied to Tate 4.1.2 and 4.1.5; minus transpose ensures the monodromy squares. |
| `TwistCompatibility` | Sum distributivity, multiplication of the two tensor characters, inverse character on duals, successive twists and the trivial twist. Derived from scalar action and unchanged monodromy in the same tensor convention. |
| `CorrectionCompatibility`, `CorrectionAtCompatibility` | Sum/tensor corrections are product/tensor automorphisms; the dual correction is inverse transpose, and a scalar twist leaves it unchanged. Derived from multiplicative Jordan decomposition and its unipotent/semisimple characterizations in Deligne 8.5 and Tate 4.1.3. Both the choice-free and chosen-operator predicates are stated. |
| `SemisimplificationCompatibility` | The existing existential relation is preserved by sum, tensor, dual and twist on actual inputs and outputs. Derived by transporting the preceding correction formulas through the carrier identifications in `IsSemisimplificationAlong`. |
| `FrobeniusSemisimplicityCompatibility` | Sum is Frobenius semisimple iff both factors are; tensor preserves it; dual and twist preserve it in both directions. Derived from diagonalizable complex operators. Tensor reflection is deliberately not claimed, since a factor can have rank zero. |
| `KernelCorrection` | An actual correction restricts to an automorphism of the actual monodromy kernel, commuting with its inclusion, and is a correction of its zero-monodromy pair. Tate 4.1.3 and 4.1.5; Deligne 8.5. |
| `KernelSemisimplification` | The Weil action on the output kernel is a semisimplification of the Weil action on the input kernel. The representation is compared via zero-monodromy embedding, not merely by equal dimension or underlying subspace. Derived from restriction of the correction. |
| `FiniteInertiaPreservation` | Finite inertia image survives the four operations and the kernel. Twists explicitly require finite image of the character on inertia, without any whole-image finiteness or unitarity assumption. Direct finite-image algebra from the operation formulas and Tate's inertia convention. |
| `ParameterPreservation` | Under an explicitly supplied topological-group structure (its own binder `[IsTopologicalGroup G]`), the open-inertia-kernel condition survives the same operations; the twisting character has open kernel on inertia. This is a separate preservation statement using finite intersections and subgroup inclusions, not a continuity comparison. |
| `ContinuityPreservation` | Usual complex finite-dimensional continuity survives the operations and restriction to the kernel. The character is explicitly continuous. Finite-dimensional linear and bilinear maps supply continuity of the sum, tensor, twist and kernel actions. The dual action `g ↦ ρ(g⁻¹)ᵀ = (ρ(g)⁻¹)ᵀ` is continuous because inversion of invertible endomorphisms and transposition are continuous. This clause also carries the explicit binder `[IsTopologicalGroup G]`, as a uniform sufficient hypothesis (see below). |
| `AlgebraicFamily`, `Statement` | Conjunctions of precisely the clauses above. `AlgebraicFamily` needs no topology. `Statement` has its own binder `[IsTopologicalGroup G]` and adds the two distinct topological preservation conditions. |

The three topological declarations carry `[IsTopologicalGroup G]` as their own
binder, not as a section variable. Their bodies do not use the instance, and
Lean omits an unused section instance variable from a definition's type.

For `ParameterPreservation`, and hence `Statement`, the hypothesis is
necessary. Take `G` cyclic of order 4 with generator `a` and the topology
`{∅, {1}, G}`, which is not a group topology, with `I = G`. Let `χ(a) = i` and
let `A` and `B` be the rank-one pairs with action `χ` and zero monodromy. Both
have open inertia kernel `{1}`, and so does `χ`, but `tensor A B` and
`twist χ A` act by `χ²`, whose kernel `{1, a²}` is not open.

This example does not refute `ContinuityPreservation`. Its character `χ` is not
continuous: a small complex neighborhood of `i` pulls back to `{a}`, which is
not open, so the continuity premises fail. For that clause the binder is not
needed, by the argument in the table. It is retained there as a uniform
sufficient hypothesis, so that one topological-group binder governs all three
topological declarations. It holds in every intended application, since the
local Weil group is a topological group.

The kernel subspace is transported exactly under semisimplification as
recorded in `Frobenius.Invariants`. Its restricted Weil action need not
remain equal. The present kernel targets identify the corrected action
through an actual linear identification. Rank, all powers of `N`, their
kernels and images, and determinants remain covered by that existing
invariant family; this file does not replace them by a dimension-only claim.

## Exact registered originals

- `deligne-1973-local-constants`,
  SHA-256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*
  (1973), §§8.4–8.6, internal/PDF pages 68–70; especially 8.4.3 and 8.5,
  equation (8.5.1). The operation consequences above are derived statements,
  not additional numbered assertions attributed verbatim to Deligne.
- `tate-1979-number-theoretic-background`,
  SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  John Tate, *Number theoretic background*, Corvallis Part II (1979),
  §§4.1.1–4.1.6, printed pages 20–21, retained PDF pages 29–30.
- `henniart-2002-characterization`,
  SHA-256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`:
  Guy Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)* (2002), §2.1, printed page 593, retained PDF page 7.

Worker 1 read these original passages and checked the relevant formulas
visually; the same retained source copies support the first two statement
families. Arithmetic-factor identities in Henniart 2.1 belong to a separate
task. No arithmetic-factor statement or block classification is asserted here.

## Related Library results

- `Langlands.Weil.RepresentationOperationClosure`
  (`Langlands/Weil/Representation/Operations.lean`) is a Weil-level statement
  target, proved as `representationOperationClosure` in
  `Langlands/Weil/Representation/OperationClosureProof.lean`. It covers
  continuity, open inertia kernels and finite images of the underlying sum,
  tensor, dual and twist representations. Once the underlying
  representations of the actual pair operations are identified with
  Mathlib's `prod`, `tprod` and `dual` and the scalar twist (by `Formulas`),
  it gives the sum, tensor, dual and twist clauses of
  `FiniteInertiaPreservation`, `ParameterPreservation` and
  `ContinuityPreservation`. The clauses for the monodromy-kernel
  representation are not covered there. The present targets
  are phrased for Weil–Deligne pairs; neither family replaces the other.
- `Langlands/Weil/Representation/InertiaOperations.lean` proves the
  open-inertia-kernel closure of sum, tensor, dual and twist on underlying
  representations. A future proof can reuse it.
- `Langlands.WeilDeligneRepresentation.LinearAlgebra.IsomorphismInvariants`
  and `Frobenius.Invariants` cover rank, powers of `N`, their kernels and
  images, and determinants along isomorphisms and semisimplification. This
  file does not restate them.

## Dependencies

The operation constructors are Worker 17's published work for the companion
definition task `650de61a-84c3-40d1-b791-0544af5824e1` (this task's context
cites it by its earlier identifier `503968de-16f8-4f63-ba13-b5e167e11dce`).
Worker 17 retains authorship of those sources; they are imported, not
included here as new authored content. This statement imports these modules
from the Library at commit `0aa8ebf100fddc512af4406817bcd1730dd75f75`, with
these Lean hashes:

- `Langlands/WeilDeligne/FrobeniusStatements.lean`:
  `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa`.
- `Langlands/WeilDeligne/SumsTensor.lean`:
  `b022cece208c2429280b3485628442f05da9e0097cb1fb558448a36bc6e0c06d`.
- `Langlands/WeilDeligne/Dual.lean`:
  `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9`.
- `Langlands/WeilDeligne/Twist.lean`:
  `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0`.
- `Langlands/WeilDeligne/Kernels.lean`:
  `fc80f9ec895d5bfbc1ae4b397c799aa657eac45b2a4154be30a0fc8f5d560da6`.

Through these it uses the pair core `Langlands.WeilDeligne.{Basic,Parameters}`
and the finite-representation modules
`Langlands.Weil.Representation.{Basic,Predicates,SumsTensor,Dual,Twist,Invariants}`.

## Revision

Version 2 corrects the first published version, candidate
`5c4b2352-e9d4-4fe7-a3e4-dd89c1119913`. There, `[IsTopologicalGroup G]` was a
section variable, so Lean left it out of `ParameterPreservation`,
`ContinuityPreservation` and `Statement`, contrary to this Markdown. By the
example above, `ParameterPreservation`, and hence `Statement`, was false.
No counterexample is claimed for version 1 of `ContinuityPreservation`.
Reviewer 153 found the same defect in the sibling family
`ParameterRelationStatements` (rejected candidate
`d1deba2f-d04e-4d11-b9ae-68e74d90543e`). Worker 1 then confirmed it here with
a private probe. Only these three binders changed. All other declarations and
their types are unchanged. At Library commit
`0aa8ebf100fddc512af4406817bcd1730dd75f75` no other Lean module imports this
file or uses its declarations, so the changed types affect no downstream
statement. Reviewer 198 independently found the defect and
published correction task `69aa0940-38d2-4b90-a62a-74400926bb5b`; this
version addresses it.

An earlier version-2 candidate, `c258de01-5d66-41ef-83a9-e601414f720f`, had the
same Lean file. Reviewer 201 rejected it because its Markdown wrongly said that
the C4 example also refutes `ContinuityPreservation`. This Markdown corrects
that explanation.

## Check

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` v1:
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `5e74b65c-98de-4934-a98a-852899ddf5fa` compiled this module
over that Library commit with no errors or warnings. It inspected
`Langlands.WeilDeligneRepresentation.OperationLaws.Statement`, confirmed
`statement_returns_prop: true`, and returned whole-target SHA-256
`2d6d73f00414b94df21bd5aa1a04d91c757bf4bece902070213531d5e0ff4b23` and type
SHA-256 `0297f420b40ed79148dc82bcd257bf221e3d8225e132a73ea97706ceab0f7311`.
The checked Lean SHA-256 is
`acfaa88b6e9073af019b74dedc2ffde341e581186b30831040e3dbbdc0b395fe`.
Its independent universes are `uG`, `uV`, `uW`, `uX` and `uY`; its axioms are
`propext`, `Classical.choice` and `Quot.sound`. This is development evidence;
independent semantic acceptance and Library publication remain outstanding.
