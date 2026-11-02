# Rank one reflected along a fibrewise flat local map

For local ring maps `R → A → B`, a finitely presented `A`-module `M`
that is flat over `R`, and an essentially finitely presented map `R → A`,
the construction reflects rank one of `B ⊗[A] M` to rank one of `M`.
The additional hypothesis is flatness of
`F → F ⊗[A] B`, where `F = A ⊗[R] κ(R)` is the actual residue fibre.

This is an internal consequence of `LocalFiberRankOne`, with no additional
literature assertion. Commuting and cancelling tensor products identifies
`F ⊗[A] B` with `B ⊗[R] κ(R)`, so it is a local ring. The inclusion of
`F` is local because `A → F` is surjective and its composite is the
local map `A → B` followed by the surjective residue base change.
Extending the supplied basis to this local fibre ring and cancelling
scalar extensions gives the input for
`linearEquivOfResidueFiberBaseChange`.

All four universes are independent. The output is a choice of a linear
equivalence, with no compatibility asserted with the supplied basis.
