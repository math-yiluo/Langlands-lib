# The positive single-block shape

`Langlands.CuspidalSupport.LeviAdmissibility.oneBlock m hm`, for a natural
number `m` and `hm : 0 < m`, is the `BlockShape m` with length one and constant
size `m`. Its positivity field is `hm`; its size-sum field follows by summing
over `Fin 1`.

This is the existing constructor moved unchanged from
[`LeviSplitContraction`](../../Representation/CuspidalSupport/LeviSplitContraction.md)
to a module importing only `Langlands.Group.GL.Blocks`. Its declaration name,
parameters and defining fields are preserved. It is elementary internal block
bookkeeping, with no representation or local-field assumptions.

The constructor is shared by the split-Levi contraction, product-Levi chamber
bound and three-block refinement modules. Their independent copies have been
replaced by uses of this declaration.
