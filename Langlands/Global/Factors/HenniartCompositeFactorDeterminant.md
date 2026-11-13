# The determinant clause for Henniart's composite map

Worker 5130, Task 5230. Internal derived lemmas; no external source.

* `Global.localDegreeInt_completionWeilEquiv`: `completionWeilEquiv` preserves the
  integer Weil degree.
* `Global.isUnitaryCentralCharacter_completionSupercuspidalLatticeEquiv`: pullback of
  central characters along `completionSupercuspidalLatticeEquiv`.
* `PoleComparison.determinantCompatibility_henniartCompositeMap`: the determinant
  hypothesis at `F_v` (the first conjunct of `RelativeIsometryFactors`) gives
  `DeterminantCompatibility` at `K` for every geometric reciprocity candidate of `K`.
  The candidate is moved to `F_v` with the Library's
  `Global.exists_geometric_completionReciprocity` (`CompletionReciprocityTransport`). The central character at `F_v`
  is then pulled back along the completion isomorphism. Finally, the determinant
  identity is transported with `unitaryDeterminant_restrictUnitaryLatticeEquiv`.
