# Kostant's theorem: final assembly (conditional form)

* `glProductWhittaker_of`: Kostant's theorem for all finite products of `𝔤𝔩_{n i}(ℂ)`, the
  Library proposition `GLProductWhittakerMaximallyFaithfulStatement` (module
  `Langlands.Representation.Archimedean.GLProductWhittaker`), follows from the nilpotent cone
  statement and the orbit statement. Decidable equality of the index type is supplied
  classically, and the proof applies `maximallyFaithful_of`.
* `realWhittaker_of`: `RealWhittakerMaximallyFaithfulStatement` follows from the same two
  statements for one-block products. Given `π`, its infinitesimal character and the data of
  `IsRealGenericGKModule`, the proof transports along `toGL n`
  (`hasInfinitesimalCharacter_comp`, `isWhittaker_comp`) and applies `maximallyFaithful_of`
  with coefficients `i a_p`; these are nonzero because `a_p ≠ 0`. It then transports maximal
  faithfulness back with `isMaximallyFaithful_of_comp`.
