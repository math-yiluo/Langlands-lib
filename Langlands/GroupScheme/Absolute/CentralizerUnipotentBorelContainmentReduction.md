# Reducing centralizer Borel containment to two structural statements

`Langlands.GroupScheme.centralizerUnipotentBorelContainment_of_statements`
proves `CentralizerUnipotentBorelContainmentStatement.{u}` from two hypotheses:

- `CentralizerBorelIntersectionStatement.{u}`: a Borel subgroup `B` of `G` that
  contains the cocharacter `χ` contains a Borel subgroup `C` of the represented
  centralizer `M`. This is the existence part of Milne 2017, Theorem 17.46.
- `NormalUnipotentBorelContainmentStatement.{u}`: a smooth connected unipotent
  normal closed subgroup lies in every Borel subgroup. This is the unipotent case
  of Milne 2017, Remark 17.31.

## Proof

Fix the data of the target: `k`, `G`, `χ`, a smooth connected closed
representative `j : M ⟶ G` of the centralizer, a smooth connected unipotent
normal closed subgroup `i : U ⟶ M`, and a Borel subgroup `b : B ⟶ G` containing
`χ`.

1. The first hypothesis gives a Borel subgroup `c : C ⟶ M` with
   `range (c ≫ j) ≤ range b`.
2. The second hypothesis is applied with `H := M`. Its instance arguments are
   smoothness and connectedness of `M`, which are premises of the target. The
   third is `IsAffineHom M.X.hom`, which follows from closedness of `j` by
   `IsClosedSubgroup.isAffineHom`. The result is `range i ≤ range c`.
3. `SubgroupFunctor.range_comp_mono` pushes this containment forward along `j`,
   giving `range (i ≫ j) ≤ range (c ≫ j)`. Transitivity with step 1 gives
   `range (i ≫ j) ≤ range b`.

The proof does not use the scheme-theoretic image of `χ`. The cocharacter form of
the first hypothesis already contains any comparison with the image torus.
