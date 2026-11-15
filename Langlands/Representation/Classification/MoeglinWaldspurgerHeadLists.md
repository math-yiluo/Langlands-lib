# Products of segment heads along lists of intervals

Module `Langlands.Representation.Classification.MoeglinWaldspurgerHeadLists`, namespace
`Langlands.MoeglinWaldspurger.Derivation`. Internal infrastructure for the derivative-comparison
proof of the Moeglin–Waldspurger algorithm; no new mathematics. `CastIso` means
"isomorphic after the literal rank transport" (`MoeglinWaldspurgerCastCalculus`).

## Rank-zero factors and associativity

* `PosOrIrr T Y`: the rank of `Y` is positive, or it is zero and `Y` is irreducible.
* `castIso_rankZero_left`: an irreducible rank-zero left factor `W` satisfies `W × X ≅ X`.
  Proof: `rankZeroIrreducibleUnitIso` identifies `W` with the binary unit, and the Library's
  `SegmentProductOrderedAssembly.leftUnitIso` removes the unit.
* `CastIso.isIrreducible`: irreducibility transfers along `CastIso`.
* `castIso_assoc''`: `(A × B) × C ≅ A × (B × C)` for `A` of positive rank and `B`, `C`
  satisfying `PosOrIrr`. If `B` has positive rank this is `castIso_assoc'`. Otherwise both sides
  are `A × C` by the rank-zero unit lemmas.
* `posOrIrr_binary`, `posOrIrr_of_isIrreducible`: closure facts. A product of two rank-zero
  irreducible factors is the first factor, by `castIso_rankZero_right`.
* `castIso_iterProd_binary`: `(B^K × Y) × Z ≅ B^K × (Y × Z)`, by induction on `K` with
  `castIso_assoc''`.

## Heads along lists

* `segHead F ρ x I`: the Library's chosen head `T.segmentHead` of the realized segment of the
  interval `I`. `segHead_isSegmentHead` holds because every segment has a segment head
  (`segmentSpecialConstituentExistence`) and `T.segmentHead` is then one
  (`IsSegmentHead.isSegmentHead_segmentHead`). It is irreducible (`segHead_isIrreducible`).
* `listRank ρ x l m` and `listProd F ρ x l Y = L(I₁) × (L(I₂) × ⋯ × (L(I_k) × Y))`: the
  right-nested binary product of the chosen heads along the list `l` with a tail `Y`.
* `consHeads F ρ x l d`: the segment-product datum obtained by prepending the chosen heads along
  `l` to `d`, using `SegmentProductOrderedAssembly.cons`.
* `consHeads_induced`: its induced representation is `listProd` of the tail's induced
  representation. Proof by induction with `nonempty_cons_iso_binary`.
* `consHeads_segments`: its list of segments is `l.map (realize ρ x)` followed by those of `d`.
* `consHeads_hasSegmentHeads`, `cons_hasSegmentHeads`, `empty_hasSegmentHeads`: the blocks are
  segment heads.
* `listRank_eq`: `listRank ρ x l m = weight l * ρ.rank + m`.
