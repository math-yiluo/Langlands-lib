# Proof of the reduction of canonical contragredient commutation

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalContragredientCommutationReductionStatement`
(module `CanonicalRationalTheorem17ReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalContragredientCommutationReduction :
  CanonicalRationalContragredientCommutationReductionStatement.{u, v}`.

The statement has three inputs. The first is the class form of induced Weyl
conjugacy, `RationalInducedClassWeylConjugacyStatement.{u, v}` (Aubert (1995),
identity (1.2)). The other two are the finite-length-implies-admissible targets
(Renard, Théorème VI.6.3) for `G(F)` and for every dynamic Levi,
`RationalPointsFiniteLengthAdmissibleStatement` and
`DynamicLeviFiniteLengthAdmissibleStatement`, both at `.{u, max (u + 1) v}`.
Together they imply `CanonicalRationalContragredientCommutationStatement.{u, v}`,
Théorème 1.7 (1) for the canonical actual operator. That conclusion keeps its
own binders: the two dynamic finite-length hypotheses `hiFl`, `hrFl` and the
per-group hypothesis `hc` that the contragredient preserves finite length. The
statement module's Markdown describes the statement, its meaning and its
provenance. This file describes only the Lean proof. The proof takes the three
inputs as hypotheses, does not prove or weaken any of them, and uses no further
hypothesis.

## Proof

The tactic proof introduces `hWeyl`, `hadmG` and `hadmM`, in the order of the
statement's inputs, then:

1. The published theorem
   `rationalContragredientCommutation_of_admissibility_and_inducedWeyl`
   (module `RationalContragredientAssembly`) proves
   `RationalContragredientAssemblyStatement.{u, v}`. That statement takes the
   same three propositions at the same universes, but in the order
   admissibility for `G(F)`, admissibility for dynamic Levis, class Weyl
   conjugacy. It is applied to `hadmG`, `hadmM` and `hWeyl`, in that order,
   giving `hcomm : RationalContragredientCommutationStatement.{u, v}`.
2. The published theorem `canonicalRationalTargetBridges`
   (module `CanonicalRationalTargetBridgesProof`) proves the conjunction
   `CanonicalRationalTargetBridgesStatement.{u, v}`. Its first conjunct `.1` is
   the implication
   `RationalContragredientCommutationStatement.{u, v} →
   CanonicalRationalContragredientCommutationStatement.{u, v}`; applying it to
   `hcomm` closes the goal.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`f22cb810d733066a219c9a7db2ea38892a973f85`). Against that Library, the module compiles with
zero errors and zero warnings. The theorem has universe parameters `u`, `v`
and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
