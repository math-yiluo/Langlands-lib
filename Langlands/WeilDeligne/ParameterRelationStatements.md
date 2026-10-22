# Targets for dual and twist relations on parameter classes

Worker 1 authored this statement family for task
`4bcfd048-60a1-4be4-a737-2fb8c48efc46`. It states targets for the common
class relations `ParameterRelations.IsDualOf` and `IsTwistOf`, whose design
Worker 7 proposed and Worker 25 coordinated. The target is
`Langlands.WeilDeligneRepresentation.ParameterRelationLaws.Statement`.
Every result is a proposition definition, not a proof and not an assumed
classification. Downstream correspondence statements use the exact
quotient-equality relations in the separate `ParameterRelations` definitions.

## Scope and hypotheses

Inputs are the existing rank-indexed Frobenius-semisimple complex parameter
classes `FrobeniusSemisimpleParameterClassesOfRank (ν := ν) I degree n`.
These are isomorphism classes of actual finite-dimensional complex pairs with
nilpotent monodromy, open inertia kernel and rank `n`. Frobenius
semisimplicity means that every element of nonzero degree acts
semisimply; monodromy may be nonzero. The group and vector-space universes
`uG` and `uV` are independent. Every natural rank is allowed, including zero.
The degree and norm characters are arbitrary. The closure statements use no
Frobenius-correction existence theorem, no surjectivity of degree and no
assumed numerical norm formula.

The dual has exactly the same inertia kernel as the original. A transpose is
the identity exactly when the original map is, and `g` and `g⁻¹` lie in the
same kernel. The dual closure statements therefore need no compatibility
between the group structure and the topology. Twisting is different: the
twisted inertia kernel contains the intersection of the representation's and
the character's inertia kernels. In a topological group, a subgroup containing
an open subgroup is open. The twist preservation, existence and
unique-existence targets therefore explicitly assume
`IsOpen ((χ.comp I.subtype).ker : Set I)` and `[IsTopologicalGroup G]`.
`TwistPreservation`, `TwistExistence`, `TwistUniqueExistence` and `Statement`
each declare `[IsTopologicalGroup G]` as their own binder. No definition body
uses that instance, and Lean omits an unused section instance variable from a
definition's type, so a section variable would leave the hypothesis out.
Without it the twist targets are false (see Revision below).
Usual complex continuity does not replace this hypothesis, and the present
algebraic parameter type does not require it. A local specialization must
establish the hypothesis for its own characters. This file adds it to no
local correspondence assertion.

Uniqueness, rank and the laws about given outputs need no closure assumption
on the character. This does not give totality for arbitrary characters. The
unrestricted output class always exists, but membership in the restricted
parameter set is a separate mathematical claim.

## Declaration-level source and dependency map

All names below belong to
`Langlands.WeilDeligneRepresentation.ParameterRelationLaws`.

| Declaration | Content and provenance |
| --- | --- |
| `ForgetInjective` | For each `I`, `degree` and `n`, `ParameterRelations.forget` is injective. A subtype quotient by the restricted pair-isomorphism relation embeds in the original quotient, and fixing the rank does not change this. Internal quotient reasoning from the companion `Setoid.comap` definitions. |
| `RepresentativeCharacterizations` | If `forget D` and `forget E` are the classes of `A` and `B`, then `IsDualOf D E` holds exactly when `B` is equivalent to `dual A`, and `IsTwistOf χ D E` holds exactly when `B` is equivalent to `twist χ A`. The equivalences are genuine pair equivalences, as in Tate 4.1.2; this is internal quotient reasoning. |
| `ClassRankPreservation` | Dual and twist preserve rank on unrestricted pair classes. The dual of a finite-dimensional space has the same dimension, and a twist keeps the carrier. Henniart2002 1.2 places the contragredient in the same `G(n)`. |
| `RankNormalization` | For a rank-`n` input, the original, dual and twisted unrestricted classes all have rank `n`, for every character. This is the rank condition of the output subtype, stated separately from its other conditions. |
| `DualUniqueness`, `TwistUniqueness` | For a fixed input and operation, there is at most one restricted output. Derived from quotient equality and `ForgetInjective`. |
| `DualPreservation` | The actual dual (inverse-element action, minus transpose monodromy) preserves the open inertia kernel, Frobenius semisimplicity and rank. A degree-nonzero `g` has `g⁻¹` of nonzero degree, and the transpose of a semisimple operator is semisimple. Finite-dimensional duality applied to Tate 4.1.2–4.1.3. |
| `DualExistence`, `DualUniqueExistence` | The dual has an output, and a unique one, in the same rank-indexed parameter set, with no selected dual function or closure axiom. Derived from dual preservation and quotient reasoning. |
| `InverseLaws` | The dual relation is symmetric (biduality), the trivial twist relates a class only to itself, and twisting by `χ` is undone by twisting by `χ⁻¹`. Stated for the actual class relations and derived from finite-dimensional evaluation duality and scalar cancellation. |
| `TwistComposition` | Twisting by `χ` and then `ψ` is twisting by `ψ * χ`. Derived from the scalar-twist convention, tensoring by a one-dimensional zero-monodromy character (Tate 4.1.2, 4.1.5). |
| `DualTwistCompatibility` | Duals of a twist pair are twisted by the inverse character. Derived from the inverse-element dual action and the scalar-twist convention. |
| `TwistPreservation` | With an open character inertia kernel and a topological-group structure (explicit binder `[IsTopologicalGroup G]`, as in the next two rows), the actual twist preserves the open inertia kernel, Frobenius semisimplicity and rank. The topological step is the open-subgroup argument above; the Frobenius step multiplies a complex semisimple operator by a nonzero scalar. |
| `TwistExistence`, `TwistUniqueExistence` | Under exactly that open-kernel premise, a twisted output exists in the restricted set, and it is unique. Preservation is a separate conclusion of the family and is never assumed in these premises. |
| `AlgebraicFamily`, `Statement` | Conjunctions of the displayed targets. `AlgebraicFamily` collects the twelve targets that need no topological-group structure. `Statement` has its own binder `[IsTopologicalGroup G]` and adds the three twist closure targets under it. |

The pair operations, quotients and forgetful maps are imported from the
companion definitions, and the relations from `ParameterRelations`. Nothing
depends on block classification, automorphic representations, local
reciprocity or a chosen Frobenius-semisimplification function.

## Related Library results

Worker 17's published `Langlands.WeilDeligne.ParameterOperations` defines the
actual operations `parameterDualClass` and `parameterTwistClass` on the
open-inertia classes `ParameterClasses`, without Frobenius semisimplicity or
rank. Their open-kernel certificates are the proved theorems
`FiniteRepresentation.hasOpenInertiaKernel_dual` and
`hasOpenInertiaKernel_twist` in `Langlands.Weil.Representation.InertiaOperations`.
Both theorems assume `[IsTopologicalGroup G]`. A proof of
`TwistPreservation`, which has that binder, can reuse
`hasOpenInertiaKernel_twist` for the open-inertia component. `DualPreservation`
has no such binder, so its proof should use the kernel equality described
above instead of `hasOpenInertiaKernel_dual`. The Frobenius-semisimplicity
components, the rank conditions and all statements about the relations
on `FrobeniusSemisimpleParameterClassesOfRank` remain targets here.
The object-level operation laws of the separate family
`Langlands.WeilDeligneRepresentation.OperationLaws`
(`Langlands/WeilDeligne/OperationStatements`) motivate these quotient
targets but are neither imported nor assumed.

## Exact registered originals

- `henniart-2002-characterization`, Guy Henniart, *Une caractérisation de la
  correspondance de Langlands locale pour GL(n)* (2002), §1.1 and the remark
  in §1.2, printed pp. 588–589 / retained PDF pp. 2–3; §2.1, printed p. 593 /
  PDF p. 7. SHA-256:
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `tate-1979-number-theoretic-background`, John Tate, *Number theoretic
  background*, Corvallis Part II (1979), §§4.1.2–4.1.5, printed pp. 20–21 /
  retained PDF pp. 29–30. SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Worker 1 read and visually checked these original passages. The table
labels the quotient and topology consequences as derived; none is attributed
to the sources as an additional numbered theorem. Rank zero is an internal
extension of Henniart's positive-rank convention.

## Dependencies

This pair imports only `Langlands.WeilDeligne.ParameterRelations`, from the
Library at commit `00f9ac4d66cfd40043d36dbe31ea364e1316cde9`. Through it, the
pair uses Worker 17's published quotients and operations from the companion
definition task `650de61a-84c3-40d1-b791-0544af5824e1` (this task's context
cites it by its earlier identifier `503968de-16f8-4f63-ba13-b5e167e11dce`).
These modules are imported, not reauthored here. Their Lean hashes are:

- `Langlands/WeilDeligne/ParameterRelations.lean` (`forget`, `IsDualOf`,
  `IsTwistOf`):
  `29d82698b08437c8230780ae06d36818cc62708cf164be30aa9ea6bb77a00c66`.
- `Langlands/WeilDeligne/Parameters.lean`
  (`FrobeniusSemisimpleParameterClassesOfRank`,
  `IsFrobeniusSemisimpleParameter`):
  `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c`.
- `Langlands/WeilDeligne/Dual.lean` (`dual`, `dualClass`):
  `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9`.
- `Langlands/WeilDeligne/Twist.lean` (`twist`, `twistClass`):
  `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0`.
- `Langlands/WeilDeligne/Basic.lean` (`WeilDeligneRepresentation`, `Equiv`,
  `classOf`, `classRank`, `rank`):
  `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf`.

## Revision

This version replaces candidate `d1deba2f-d04e-4d11-b9ae-68e74d90543e`.
In its review, Reviewer 153 found that `[IsTopologicalGroup G]` had been a
section variable, which Lean dropped from the four twist-closure declarations
because no body uses it. Without the hypothesis those targets are false. Take
`G` cyclic of order 4 with generator `a` and the topology `{∅, {1}, G}`, which
is not a group topology, with `I = G` and trivial degree and norm character.
Let `χ(a) = i` and let `A` be the rank-one pair with action `χ` and zero
monodromy; it is a Frobenius-semisimple parameter of rank 1. Then `χ` and `A`
both have inertia kernel `{1}`, which is open. But the twist `twist χ A` has
action `χ²` and inertia kernel `{1, a²}`, which is not open. Isomorphic pairs
have equal inertia kernels, so no restricted class is a twist output either,
and the existence targets fail as well. The four
declarations now carry the binder explicitly, and the elaborated types contain
it. Reviewer 153 judged all other clauses correct, and they are unchanged.

## Check

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` v1:
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `9586c0e2-0ce4-48ee-b33d-34dbf1317922` compiled this module
over that Library commit with no errors or warnings and inspected the complete
target. It reported `statement_returns_prop: true`, universes `uG` and `uV`,
whole-target SHA-256
`adfeaf54e46a2b53a3ceef10ec13d336e607ec88703e44fd12b7b5a2ba2f0c33` and type
SHA-256 `864774df4365096a0c315affc693f15c6e708881823a12d72151b01861c6351b`.
The checked Lean SHA-256 is
`d64c91bcadfaf0a3250250cb1bc1ddfe177ca2a2c91d370eec404d4f2ea87a0e`.
Only `propext`, `Classical.choice` and `Quot.sound` appear in the
declaration inspection. This is development evidence, not mathematical
acceptance. Proofs of the targets are separate tasks on the published target.
