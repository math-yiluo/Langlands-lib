# Standard Hecke operators as finite sums over left cosets

Module `Langlands.Representation.Unramified.StandardHeckeSum`, namespace
`Langlands.Unramified`.

Let `F : PadicField p` carry its canonical topology and valuation, and let
`K = sphericalSubgroup F r = GL_(r+1)(O_F)`. This module specializes `MinusculeCosets` to
the canonical uniformizer and to lifts of residue classes. It then evaluates the standard
double-coset operators `standardHeckeElement F r i` of `HeckeOperators` on `K`-fixed vectors.

## Residue lifts

- `residueFieldFintype` is a global `Fintype` instance on
  `F.canonicalTopologicalData.ResidueField`. It is obtained from the Library fact
  `finite_residueField`.
- `uniformizerUnit_isUniformizingElement`: the canonical uniformizer
  `F.canonicalTopologicalData.uniformizerUnit` is a uniformizing element of the canonical
  valuation. The proof transports the valuation to `ℤₘ₀` through
  `valueGroupWithZeroIsoInt`, where the uniformizer has value `exp (-1)`
  (`uniformizerUnit_zpow_value`).
- `residueLift x` is an integral lift of the residue class `x`, chosen with
  `Function.surjInv`.
- `residueLift_eq_of_lt_one`: distinct classes have lifts at distance one.
- `exists_residueLift_lt_one`: every integral element is congruent to a lift. These are
  exactly the two hypotheses of `labelledRep_unique` and `exists_labelledRep`.

## The standard diagonal

`initialSegment r i` is the set of the first `i` coordinates, and `card_initialSegment`
states that it has `i` elements. `standardDiagonal_eq_subsetTorus` identifies
`standardDiagonal F r i` with `subsetTorus ϖ (initialSegment r i)`.

## The finite sum

`standardHecke_cornerAction_eq_sum`: let `ρ` be any smooth complex representation of
`GL_(r+1)(F)`, let `i : Fin (r + 2)`, and let `v` be a `K`-fixed vector. Then

`cornerAction (sphericalHaar F r) ρ hρ K _ (standardHeckeElement F r i) v
  = ∑ α : CosetIndex ResidueField (r + 1) i, ρ (labelledRep ϖ (residueLift F) α) v`.

The proof unfolds the corner action to the integrated action. It then applies
`Hecke.integratedAction_eq_sum_of_presentation` with the sets `s α = x_α K` (each of Haar
mass `1` by left invariance and `sphericalHaar_self`) and the vectors `ρ(x_α) v`. The
pointwise presentation holds for the following reasons.

- For `y` in the double coset, `exists_labelledRep` gives a representative with
  `y ∈ x_α K`, and `labelledRep_unique` shows it is the only one. Then
  `ρ(y) v = ρ(x_α) v` because `v` is `K`-fixed.
- For `y` outside the double coset, `y` lies in no `x_α K`, because every `x_α K` is
  contained in the double coset by `labelledRep_mem_doubleCoset`.
