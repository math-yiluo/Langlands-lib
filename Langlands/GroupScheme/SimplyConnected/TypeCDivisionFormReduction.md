# Reduction of the type-C division-form classification to four prerequisites

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`).

## Result

`Langlands.GroupScheme.typeCDivisionForm_of_inputs.{u}` proves
`TypeCDivisionFormStatement.{u}` from the four propositions

- `TypeCQuasiSplitInnerFormStatement.{u}` (a simply connected group with index data of type
  `C_n` has a quasi-split inner-form presentation with model `Sp_{2n}`);
- `SymplecticInnerFormAntihermitianStatement.{u}` (such a group is isomorphic to
  `σ.symplecticGroup H` for a central division algebra `D`, an involution `σ` and an
  invertible trace-valued antihermitian `H`, with the degree and dimension conditions);
- `AntihermitianSymplecticSplitRankStatement.{u}` (the split rank of `σ.symplecticGroup H`
  is `σ.wittIndex H`);
- `TypeCDistinguishedVerticesStatement.{u}` (the distinguished vertices are those numbered
  `j * degree` for `1 ≤ j ≤ σ.wittIndex H`).

The reduction is an implication between propositions; it proves none of them.

## Proof

Introduce the field `K`, the group `G`, the index data `d`, the rank `n`, the numbering `e`
and the hypotheses of the target.

1. `TypeCQuasiSplitInnerFormStatement` gives `q : QuasiSplitInnerForm G` and an isomorphism
   `q.model ≅ Symplectic.groupScheme K n`.
2. `SymplecticInnerFormAntihermitianStatement`, applied to `q`, gives `degree`, `m`,
   `NeZero m`, `D` with its instances, `0 < degree`, `m * degree = 2 * n`,
   `finrank K D = degree ^ 2`, `σ` with the symmetric-space dimension, `H` with
   `σ.IsAntihermitian H`, `IsUnit H`, and an isomorphism `iso : G ≅ σ.symplecticGroup H`.
3. The published `splitRank_eq_of_iso iso` rewrites `splitRank G` to
   `splitRank (σ.symplecticGroup H)`, which `AntihermitianSymplecticSplitRankStatement`
   identifies with `σ.wittIndex H`. This is `hrank : splitRank G = σ.wittIndex H`.
4. All witnesses of the target are those of step 2; its split-rank clause is `hrank.symm`
   and its isomorphism clause is `iso`.
5. For the vertex clause, `TypeCDistinguishedVerticesStatement` rewrites membership in
   `d.distinguishedVertices` to `∃ j, 1 ≤ j ∧ j ≤ σ.wittIndex H ∧ (e a).val + 1 = j * degree`.
   Rewriting the target's `splitRank G` by `hrank` turns its bound into
   `(j : ℕ∞) ≤ (σ.wittIndex H : ℕ∞)`, and `Nat.cast_le` closes the goal.
