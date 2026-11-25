# Prepending point segments to a segment-product datum

Module `Langlands.Representation.Classification.MoeglinWaldspurgerPointBlocks`.

* `iterProd T B j Y`: the right-nested product `B × (B × ⋯ × Y)` with `j` factors `B`, on the rank
  `powerRank r j m`; `powerProduct_eq_iterProd` identifies it with `powerProduct` for
  `B = A.obj`. `iterProd_castRank` (rank transport of `B`), `iterProd_mono` (preserves
  subrepresentations), `iterProdIso` (preserves isomorphisms), `iterProd_nontrivial`,
  `iterProd_hasFiniteLength` are proved by induction on `j`.
* `pointSegment ρ x y`: the singleton segment of `ν^{x+y} ρ`; `pointSegment_eq` identifies it with
  the realization of the point interval `[y, y]`. `pointBlock F ρ x y` is the chosen
  supercuspidal representative `cuspRep F T ρ x y`, transported to the degree of the singleton
  segment; it is a segment socle (`pointBlock_isSegmentSocle`, from the published
  `singletonSegment_isSegmentSocle`) and irreducible.
* `iterCons F ρ x y j d₀`: the datum with `j` point segments `[y, y]` followed by the datum
  `d₀`, built with the published `SegmentProductOrderedAssembly.cons`.
  `iterCons_induced` (its product is `iterProd` of the point block, via
  `nonempty_cons_iso_binary`), `iterCons_segments` (segment list) and
  `iterCons_hasSegmentSocles`.
