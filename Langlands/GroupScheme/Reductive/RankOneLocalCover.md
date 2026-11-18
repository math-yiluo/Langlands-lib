# Conditional assembly of the rank-one central cover

This internal module proves `RankOneCentralCoverStatement` from two inputs. Both are stated as
propositions in the module, not assumed as axioms. The final proof
`Langlands.GroupScheme.rankOneCentralCover` (module `Reductive/RankOneCentralCoverProof`)
discharges both.

- `RankOneLocalCover.RootCellCoverInput`: a connected reductive group `G` with a split torus
  `i : T → G`, a root cell `RootCell.IsRootCell i α αv xp xm` and `⟨α, αv⟩ = 2` admits the
  target's central cover. Its binders match Worker 919's theorem
  `rankOneCentralCover_of_rootCell` (module `Langlands.GroupScheme.Reductive.RankOneCoverOfRootCell`),
  which proves it.
- `RankOneLocalCover.LocalLineCrux`: in semisimple rank one over an algebraically closed field,
  every root `α` is positive on some cocharacter `ν` such that `α` (resp. `-α`) is the only root
  positive (resp. negative) on `ν`, and the weight spaces of `α` and `-α` are lines. It is proved
  as `RankOneLocalCover.localLineCrux` in module `Reductive/RankOneFlagCrux`.

## Proof of `rankOneCentralCover_of_inputs`

Choose a root `α` from the target's nonemptiness hypothesis. The crux gives `ν` and the four
local facts. `RankOneLocalAssembly.exists_isRootCell` turns them into a coroot `h` with
`⟨α, h⟩ = 2` and root groups `xp`, `xm` forming a root cell. The root-cell input applied to
this cell returns the target's conclusion.

## Provenance

This is internal assembly for Task 7586. It contains no mathematics beyond composing the cited
lemmas.
