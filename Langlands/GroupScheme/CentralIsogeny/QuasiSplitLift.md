# Quasi-splitness lifts along central isogenies

Author: Worker 1499. The helper module `CentralIsogeny/BorelPreimage` adapts two
lemmas from Worker 1459's `Adjoint/QuasiSplitProof.lean`; see its Markdown.

`Langlands.GroupScheme.centralIsogenyQuasiSplitLift` proves the unchanged
statement `Langlands.GroupScheme.CentralIsogenyQuasiSplitLiftStatement.{u}`
(module `CentralIsogeny/QuasiSplitLiftStatement`):

```lean
theorem centralIsogenyQuasiSplitLift : CentralIsogenyQuasiSplitLiftStatement.{u}
```

So for every field `K : Type u`, a central isogeny `π : G ⟶ A` with `G`
connected reductive and `A` quasi-split makes `G` quasi-split. The theorem has
no perfectness or characteristic hypothesis on `K`, and the kernel of `π` may be
nonreduced.

## Proof

1. Quasi-splitness of `A` supplies a geometric Borel subgroup `j : B ⟶ A`
   (`IsQuasiSplit.exists_isGeometricBorelSubgroup`). Its first component makes
   `j` a closed subgroup.
2. Let `i = SubgroupPreimage.inclusion π j : P ⟶ G` be the scheme-theoretic
   preimage of `B`. It is a closed subgroup
   (`SubgroupPreimage.isClosedSubgroup`). Connected reductivity of `G` is a
   hypothesis. It remains to show that `i` is a geometric Borel subgroup.
3. By `isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure`, it suffices
   that the base change of `i` to the algebraic closure `K̄` is a Borel subgroup.
   This descent result also needs that `i` is closed, and that `G` is affine
   (from `IsConnectedReductive`).
4. Over `K̄`, apply `CentralIsogenyBorelPreimage.isBorelSubgroup_of_range_eq_comap`
   with the following inputs:
   - the base changes of `G` and `A` are connected reductive
     (`IsConnectedReductive.baseChange_toAlgebraicClosure`);
   - the base change of `π` is a central isogeny
     (`IsCentralIsogeny.baseChange`);
   - the base change of `j` is Borel (second component of the geometric Borel
     property);
   - the base change of `i` is closed (`IsClosedSubgroup.baseChange`).
5. The range condition is a rewrite. Ranges commute with base change
   (`SubgroupFunctor.range_baseChangeHom`). The range of `i` is the preimage
   of the range of `j` (`SubgroupPreimage.range_inclusion`). Preimages commute
   with base change (`SubgroupFunctor.comap_baseChange`).

Over `K̄`, the helper lemma does the substantive work. The centre of `G`, and so
the kernel of `π`, lies in a Borel subgroup of `G`. Its image is a Borel
subgroup of `A`, which after conjugation is the given one. The fppf image
criterion then identifies the preimage with that Borel subgroup. Details are in
`CentralIsogeny/BorelPreimage.md`.

## Check record

`lean_check` diagnostic `63826810-98a4-42e8-9386-7a288cc67194` compiled this
module and `CentralIsogeny/BorelPreimage` on Library base `d2fd0b68` with
0 errors and 0 warnings. It inspected
`Langlands.GroupScheme.centralIsogenyQuasiSplitLift`, which has level parameter
`u` and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Worker 1707 restaged these unchanged Lean files for task revision 2, which
allows helper modules; they first appeared in rejected candidate
`2395d896-65b1-40a6-a6af-b0c17f9f7d85`.
