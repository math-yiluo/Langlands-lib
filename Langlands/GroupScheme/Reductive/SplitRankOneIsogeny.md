# Realization of root-datum isogenies in semisimple rank at most one

This derived unit realizes a root-datum isogeny between two connected reductive
groups over an arbitrary field `k : Type u`. Both specified maximal tori are split,
and both groups satisfy the explicit rank condition that any two actual roots are
linearly dependent over `ℤ`. The exponent of the root-datum isogeny is exactly
`ringExpChar k`. All four actual character and cocharacter lattices are finitely
generated, and both finite root data are reduced.

`torusMap_root` and `coroot_torusMap` convert the root-datum equations to equations
for the actual prescribed torus morphism. For a target root `r′`, set
`r = f.indexEquiv r′` and `q = f.rootFactor r′`. The equations are
`t ≫ P′.root r′ = q • P.root r` and
`P.coroot r ≫ t = q • P′.coroot r′`.

`exists_rankOne_isogeny` applies the published `splitRankOneRootCell` theorem to
each group at these corresponding roots. It packages the resulting two actual
root cells as `RootCell.IsRootCell` witnesses. Writing `q = (ringExpChar k)^e`,
the two lattice equations allow application of `RootCell.exists_powerIsogeny`.
The prescribed torus morphism is an isogeny by `torusMap_isIsogeny`. The conclusion
retains actual root-cell witnesses, the commuting torus square, both root
restrictions `X ↦ X^q`, and the full powered-cell restriction, together with
finiteness, flatness and surjectivity of the ambient morphism. The full possibly
nonreduced kernel is retained.

`exists_realization_rank_le_one` also handles the case with no roots: all root
factors are then vacuously one, so the published central realization theorem
applies. In the case with a root, the preceding construction applies. The result
retains the prescribed actual character pullback, cocharacter pushforward and
torus isogeny. `rankOneHom` chooses this morphism and `rankOneHom_spec` records
these properties.

The provenance is derived from the published actual rank-one root-cell theorem,
the powered-cell isogeny construction and the root-datum torus construction.
No perfectness, separability or kernel-smoothness hypothesis is added. The
universe is arbitrary. This unit establishes rank at most one; general-rank
realization and the fixed-torus extension equivalence remain separate obligations.
