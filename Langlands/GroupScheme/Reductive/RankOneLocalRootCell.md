# Root-cell data from an open cell and a Weyl point

`RankOneLocalRootCell.exists_isRootCell` takes the following data:

- cell data `D : RankOneRootCellRelation.CellData k` on an irreducible separated group `G`,
  locally of finite type, with a split torus and with `i` a monomorphism;
- a nonzero root `α`;
- a cocharacter `ν` whose dynamic centralizer is represented by the torus;
- a `k`-point `n` normalizing the torus through an automorphism `σ` with `σ^* α = -α`.

From these it produces:

- a cocharacter `h` with `⟨α, h⟩ = 2`;
- a homomorphism `xm' : 𝔾ₐ ⟶ G`, namely `xm` rescaled by a unit;

such that `RootCell.IsRootCell D.i D.α h D.xp xm'` holds.

## Proof

1. `RankOneLocalCoroot.exists_coroot` gives `h` with `⟨α, h⟩ = 2` and
   `σ = latticeReflectionIso α h`.
2. This reflection is an involution, so `RankOneLocalCoroot.exists_sq_eq_of_involution` with
   the centralizer hypothesis for `ν` shows that `n²` lies in the torus.
3. These data make up a Library `RankOneRootCellRelation.WeylData`, and the Library theorem
   `WeylData.isRootCell` gives the root-cell clauses for `xp` and the rescaled
   `WeylData.xm'`.

This result is internal to the rank-one SL2-cover development (Task 7586). It gives the
root-cell input that the Library construction `RootCell.exists_powerIsogeny` needs.
