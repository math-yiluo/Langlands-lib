# Dual and twist relations on parameter classes

Worker 1 implements, for task `4bcfd048-60a1-4be4-a737-2fb8c48efc46`, the
common relation interface proposed by Worker 7 and coordinated by Worker 25;
both are listed as coauthors for that design. The declarations are in
`Langlands.WeilDeligneRepresentation.ParameterRelations`. They reuse Worker 17's
actual quotients and operations. No new Weil–Deligne object or quotient is introduced.

For a topological group carrier `G` with its group and topology specified
separately, norm character `ν`, subgroup `I`, degree homomorphism `degree`,
and natural number `n`, the inputs are the existing
`FrobeniusSemisimpleParameterClassesOfRank (ν := ν) I degree n`.
These are isomorphism classes of actual finite-dimensional complex pairs
with nilpotent monodromy, open inertia kernel, Frobenius semisimplicity,
and rank `n`. Frobenius semisimplicity allows nonzero monodromy.
The definitions themselves need no compatibility axiom between the group
and topology, or extra assumptions on the degree or norm characters.

| Declaration | Definition and dependency |
| --- | --- |
| `forget D` | Exactly `frobeniusSemisimpleClassForget I degree D.val`, in the existing unrestricted `IsomorphismClasses ℂ G ν`. |
| `IsDualOf D E` | Exactly `forget E = dualClass (forget D)`. The actual dual uses the inverse-element dual Weil action and minus transpose monodromy. |
| `IsTwistOf χ D E` | Exactly `forget E = twistClass χ (forget D)`. The actual twist multiplies the Weil action by the scalar character and leaves monodromy unchanged. |

The subgroup, degree, rank, and norm character are inferred from `D` and `E`.
The argument order is input then output; `χ` precedes both in the twist
relation. Coefficients are complex, so taking the dual preserves the carrier
universe: `max 0 uV = uV`. The group and vector-space universes remain independent.

These equality predicates neither assert existence of an output nor choose one.
They are meaningful for every character. To obtain an output in the restricted
parameter set, the published [ParameterRelationStatements](ParameterRelationStatements.md)
targets state preservation, existence, and uniqueness as proposition definitions.
The complete target is
`Langlands.WeilDeligneRepresentation.ParameterRelationLaws.Statement.{uG, uV}`,
with independent group and carrier universes and an explicit
`[IsTopologicalGroup G]` binder. Its twist totality clauses take
`χ : G →* ℂˣ` and require `IsOpen ((χ.comp I.subtype).ker : Set I)`.
Continuity alone does not
replace this condition for an arbitrary topological group.

The intended downstream correspondence clause is nonvacuous: it existentially
quantifies a parameter output satisfying this relation and the corresponding
automorphic relation. Constructing a local reciprocity pullback and establishing
its open-inertia-kernel condition remain responsibilities of the local
specialization. No such result or local correspondence is assumed here.

## Source and derivation

These are internal quotient-level formulations of the operations on source
representations, rather than verbatim numbered assertions in the literature.

- `henniart-2002-characterization`, Guy Henniart, *Une caractérisation de la
  correspondance de Langlands locale pour GL(n)* (2002), §1.1 and the remark
  in §1.2, printed pp. 588–589 / retained PDF pp. 2–3: finite-dimensional
  complex Frobenius-semisimple representation classes of fixed rank and
  contragredience in that same rank. Section 2.1, printed p. 593 / PDF p. 7,
  records the dual operation on sums. Retained original SHA-256:
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `tate-1979-number-theoretic-background`, John Tate, *Number theoretic
  background*, Corvallis Part II (1979), §§4.1.2–4.1.5,
  printed pp. 20–21 / retained PDF pp. 29–30: pairs, morphisms,
  Frobenius semisimplicity, and tensor operations. Scalar twisting is
  tensoring by the one-dimensional character with zero monodromy.
  Retained original SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Worker 1 read these original passages and visually checked the conventions,
including the additional Henniart pp. 588–589 for this interface.
The literature's positive ranks are included; allowing rank zero is an
explicit internal extension. The actual quotient operations descend along
genuine pair isomorphisms in the companion definitions, so these predicates
require no new quotient-lift proof or closure certificate.

## Dependencies

The quotients and operations are Worker 17's published work for the companion
definition task `650de61a-84c3-40d1-b791-0544af5824e1` (this task's context
cites it by its earlier identifier `503968de-16f8-4f63-ba13-b5e167e11dce`).
They are imported, not reauthored here. This pair imports these modules from
the Library at commit `d7cf4d2d2f040f4dfa5ab22d869d51196351d821`, with these
Lean hashes:

- `Langlands/WeilDeligne/Parameters.lean`
  (`FrobeniusSemisimpleParameterClassesOfRank`,
  `frobeniusSemisimpleClassForget`):
  `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c`.
- `Langlands/WeilDeligne/Dual.lean` (`dualClass`):
  `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9`.
- `Langlands/WeilDeligne/Twist.lean` (`twistClass`):
  `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0`.

Through these it uses the pair core `Langlands.WeilDeligne.Basic` and the
finite-representation framework under `Langlands.Weil.Representation`.

This pair is a published definition layer. Its companion
`ParameterRelationStatements` family is also published. No theorem proving
the complete `ParameterRelationLaws.Statement` was found in the current
Library during this status check. Related certified constructions already
exist: [ParameterOperations](ParameterOperations.md) supplies `parameterDual`
and `parameterTwist` for open-inertia parameter objects, and
`parameterDualClass` and `parameterTwistClass` for their classes, under
`[IsTopologicalGroup G]`, with the character's open inertia-kernel hypothesis
for twisting. These do not by themselves prove the complete relation family
for Frobenius-semisimple, rank-indexed classes. This status statement makes no
claim that every individual component fact remains unproved.

## Check

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` v1:
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `9f41dc36-9f91-4b7a-85cd-34b8a105453c` compiled this module
over that Library commit with no errors or warnings. It inspected
`Langlands.WeilDeligneRepresentation.ParameterRelations.IsTwistOf`
(a `Prop`-valued definition, universes `uG` and `uV`), with SHA-256
`2d530f85e167644b22b8eb09a8828bf3a2282f5cfec836b1789da5def1cd03a5`
and type SHA-256
`c385e78a25c12c14185a69c7125c5a3458463ec7d5510752b7203a8e2c0665f9`;
its axioms are `propext`, `Classical.choice` and `Quot.sound`. This is
development evidence. Independent semantic review and publication subsequently
accepted this definition pair and the companion target family. Their publication
establishes the availability of definitions and targets, not a proof of the
complete target family.
