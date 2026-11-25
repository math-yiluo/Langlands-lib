# Deprecated names of the real branch

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv). There is no counterpart in the book.

The module `Langlands.Theta.Real.Deprecated` provides deprecated aliases (since 2026-11-23) in the
name space `Langlands.Theta` for the public declarations of `Langlands/Theta/Real/`, which are in
the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name space are in
`Langlands.Theta`), and for the standard symplectic form `Langlands.stdSymplecticForm` and its three
lemmas (`Langlands.LinearAlgebra.Symplectic`). For example `Langlands.Theta.schrodingerL2` is an
alias of `Langlands.Theta.Real.schrodingerL2`. The aliases of the two type abbreviations `RealL2` and
`RealSchwartz` are reducible, so that instances are found through them.

The aliases are in a module of their own, imported by nothing in the branch: inside the name space
`Langlands.Theta.RealMetaplecticGroup` a name `X` resolves to `Langlands.Theta.X` before the opened
`Langlands.Theta.Real.X`, so aliases in the files of the branch would shadow the declarations there.

## Content

One `alias` with the attribute `deprecated` for each of the 110 public declarations of the branch
outside `RealMetaplecticGroup` and for the four declarations of the standard symplectic form (definitions, theorems, the structure `Intertwines` with its
constructor and fields, and the instance `instHasSummableGeomSeriesEuclidean`, which as an alias is
not an instance). The aliases are listed in `Deprecated.lean`.

## Dependencies

All modules of `Langlands/Theta/Real/` that declare an aliased name (and through them
`Langlands.LinearAlgebra.Symplectic`).
