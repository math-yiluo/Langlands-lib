# Moves in iterated products

Module `Langlands.Representation.Classification.MoeglinWaldspurgerProductMoves`. Written by
Worker 5735 for Task 5735.

* `castIso_rankZero_right`: an irreducible right factor of rank zero is a unit up to rank
  transport (published `rankZeroIrreducibleUnitIso` and `SegmentProductOrderedAssembly.rightUnitIso`).
* `castIso_assoc'`: associativity when the last factor has positive rank or is an irreducible
  representation of rank zero.
* `CastIso.iterProd`, `Embeds.iterProd`: compatibility of `iterProd` with both relations.
* `castIso_iterProd_shift`: `B^K × (B × Y)` and `B^(K+1) × Y` agree up to rank transport.
* `castIso_commute`: if `Z × B` and `B × Z` agree up to rank transport, then `Z × (B^K × Y)` and
  `B^K × (Z × Y)` do, for `Y` of positive rank or irreducible (induction on `K`: associativity,
  swap, associativity, induction hypothesis).
