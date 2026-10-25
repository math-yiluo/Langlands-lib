# Ordered equal-exponent grouping

Authors: Worker 175 (original statement draft); Worker 385 (publication preparation).

`Langlands.Classification.OrderedExponentGrouping` is a `Prop`-valued
definition in
`Langlands.Representation.Classification.OrderedExponentGroupingStatement`.
It specifies finite combinatorial bookkeeping for an arbitrary
`B : GeneralLinear.BlockShape n` and an antitone function
`a : Fin B.length → ℝ`. Every block of `B` has positive size, and the sizes
sum to `n`. There is no positive-total-rank hypothesis, so the empty
rank-zero case is included.

The proposition asserts the existence of the following data and properties.

- An outer shape `D : BlockShape n` and strictly antitone real exponents
  `b : Fin D.length → ℝ`.
- A monotone surjection `q : Fin B.length → Fin D.length`, with
  `a i = b (q i)` for every old block index `i`. Thus its nonempty
  consecutive fibers are exactly the maximal equal-exponent runs.
- For each outer index `j`, a positive inner shape
  `S j : BlockShape (D.size j)` and an equivalence
  `e j : Fin (S j).length ≃ {i : Fin B.length // q i = j}`.
  The function `k ↦ (e j k).val` is strictly increasing, so this equivalence
  enumerates the entire fiber in its original order.
- Equalities `h j k : (S j).size k = B.size (e j k).val` matching every
  inner block size with its original size. Together with the sum condition
  of `S j`, these record that the new rank is the sum of the old ranks in
  the corresponding fiber.
- For every `j`, `k` and `x : Fin ((S j).size k)`, the exact equality

  ```lean
  D.index j ((S j).index k x) =
    B.index (e j k).val (Fin.cast (h j k) x)
  ```

`BlockShape.index` uses standard consecutive coordinates. The final equality
therefore identifies the nested outer/inner coordinate with the original
coordinate, with the rank transport in the displayed direction. This is the
coordinate condition used by
`Langlands.Group.GL.RefinementCoordinates` after combining the fiber
equivalences into a bijection of outer/inner labels with old block labels.

The provenance is derived internal bookkeeping: Worker 175 isolated this
finite specification for use in `SquareIntegrableEqualExponentGrouping`
from the published `Langlands.Representation.Classification.TemperedBlockStatement`.
It is not a transcription of a standalone literature theorem. The imported
`BlockShape` definitions supply the ordered sizes and standard coordinates.
This file states the proposition and supplies no proof or
representation-theoretic conclusion.
