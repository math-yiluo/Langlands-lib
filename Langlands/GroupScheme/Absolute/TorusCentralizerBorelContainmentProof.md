# Maximal-torus centralizers lie in every Borel containing the torus

Author: Worker 863.

`Langlands.GroupScheme.torusCentralizerBorelContainment` proves the unchanged
`Langlands.GroupScheme.TorusCentralizerBorelContainmentStatement.{u}` at every
universe `u`, with no additional hypotheses.

The proof constructs a closed Cartan representative `c : C → G` of the
all-test centralizer of the supplied maximal torus. The published
`cartanStructure` makes `C` smooth, connected and geometrically nilpotent.
Nilpotence implies geometric solvability.

Over the algebraically closed base field the torus is split, by
`torusFiniteGaloisSplitting` and split reflection. The published
`IsSplitTorus.exists_cocharacter_centralizer` chooses a cocharacter through
the torus having exactly the same centralizer on all scheme tests. Its
range is contained in the prescribed Borel because the torus's range is.
The published `centralizerBorelIntersection` therefore gives a Borel
inclusion `d : D → C` whose composite with `c` lies in the prescribed Borel.

Since `C` itself is smooth, connected and solvable, the maximality clause
of `IsBorelSubgroup d`, applied to the identity inclusion of `C`, makes
`d` an isomorphism. Precomposing `c` with this isomorphism does not change
its range. Thus the entire centralizer lies in the prescribed Borel.
The supplied subgroup's range lies in this centralizer, giving the
target conclusion by transitivity. This also handles the target's
possibly nonsmooth connected closed subgroup: no smoothness of that
subgroup is used.

This is an internal composition of published Library theorems. The
statement's source is J. S. Milne, *Algebraic Groups* (2017),
Corollary 17.29, printed p.360 (registered source
`milne-2017-algebraic-groups`). The implemented route uses the later
Cartan structure theorem, Proposition 17.44, and the cocharacter
existence part of Theorem 17.46 through their published proofs. It
does not use Milne's normalizer-conjugacy argument for Corollary 17.29.
The statement and all imported Lean/Markdown pairs are unchanged.
