# Lifts of continuous actions to compact quasi-étale spaces

This module proves `quasiEtaleActionLift`. Its type is the Library
statement `QuasiEtaleActionLiftStatement`, with the same universe
parameters `u`, `v` and `z`. Let a topological group `G` act
continuously on a Hausdorff analytic space `X`, and let `f : U ⟶ X` be
quasi-étale with `U` compact. Then the action lifts along `f` to a
continuous action of an open subgroup of `G` on `U`, and any two such
lifts agree on an open subgroup. This is the consequence of Berkovich's
Key Lemma 7.2 (*Vanishing cycles for formal schemes*, Invent. Math. 115,
1994) stated in §1.4 of Berkovich's 1996 manuscript.

## The reduction

`quasiEtaleActionLift_of_automorphismLift` derives the statement from
`QuasiEtaleAutomorphismLiftStatement`, which lifts near-identity
automorphisms of `X` along `f`. Let `G`, `X`, `U`, `ρ` and `f` satisfy
the hypotheses.

- The Library theorem `isRigid_of_quasiEtale` shows that `f` is rigid
  (`IsRigid f`), because it is quasi-étale with compact Hausdorff source.
  This is the uniqueness half of Key Lemma 7.2.
- Uniqueness: two lifts agree on an open subgroup by
  `ActionLift.exists_agreeOn`, which uses only rigidity.
- Existence: `nonempty_actionLift_of_automorphismLift` builds a lift
  from rigidity, the continuity of `ρ` and lifts of near-identity
  automorphisms. The lifts come from the hypothesis, applied to `X`, `U`
  and `f` with the Hausdorff, quasi-étale and compactness assumptions.

Both helper theorems are in the module `ActionLiftFromAutomorphismLifts`.

## The final theorem

`quasiEtaleActionLift` applies the reduction to
`quasiEtaleAutomorphismLift` from the module
`KeyLemma.QuasiEtaleAutomorphismLift`, which proves
`QuasiEtaleAutomorphismLiftStatement`. That proof rests on the following
modules:

- `KeyLemma.QuasiEtaleStrongNearLifts` glues local lifts into near lifts
  of strong maps (`IsQuasiEtale.hasStrongNearLifts`).
- `KeyLemma.ChartTestTransfer` transfers test triples to chart functions.
- The modules `KeyLemma.QuasiEtaleLiftChartCover`,
  `KeyLemma.LiftChartCover` and `KeyLemma.LiftCharts` provide finite
  covers by lift charts. Their local lifting constructions are in
  `QuasiEtaleActionLift`.
