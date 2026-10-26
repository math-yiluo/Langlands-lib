# Full determinant modulus under ordered refinement coordinates

`Langlands.Parabolic.RefinementCoordinatesModulusTheorem.{uF}` is a closed
proposition definition extracting the full-modulus clause of
`Langlands.Parabolic.RefinementCoordinatesNormalizationTheorem`. This module
states the assertion; its proof is a separate obligation.

The quantifiers are exactly every natural prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, natural rank `n`,
`B D : GeneralLinear.BlockShape n`, `S : Geometric.BlockRefinement D`,
and the coordinate data

- `e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length`;
- `hs : ∀ a, (S a.1).size a.2 = B.size (e a)`;
- `hc : ∀ i k x, D.index i ((S i).index k x) =
  B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)`.

Here `i`, `k` and `x` range over `Fin D.length`, `Fin (S i).length`
and `Fin ((S i).size k)`, respectively. The cast transports an inner
block coordinate to the corresponding block of `B`.

The conclusion is precisely
`RefinementCoordinatesNormalization.ModulusClause F T B D S e hs`.
Unfolding that imported definition gives

```text
∀ m : B.Levi F.Carrier,
  T.composedLeviModulus D S
      (B.leviRefinementEquiv D S e hs F.Carrier m) =
    T.leviModulus B m.
```

This is equality in `ℝ≥0ˣ`. The concrete equivalence sends the product Levi
of `B` to the actual refined Levi inside the product Levi of `D`. The
composed modulus multiplies the restricted outer modulus by the inner
block moduli. The ordinary modulus is the existing determinant-norm product
over ordered pairs of blocks of `B`.

The coordinate identity `hc` is a hypothesis of the closed assertion even
though the conclusion's helper predicate does not need it to be formed.
There is no assumed modulus identity, supplied Levi equivalence, separate
order law, positive-rank or nonempty-family hypothesis, or representation
smoothness premise. Rank zero and empty block families are included.

The provenance is an internal derivation from the published
`Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`.
For the same coordinate inputs, the combined target conjoins
`ModulusClause`, `HalfModulusClause` and `InductionClause` in that order.
This extraction keeps its entire coordinate telescope and selects only the
first conjunct. The value-space universe `uV` disappears because neither
that telescope nor the first conjunct mentions it. Consequently, a proof
of the combined target specializes at any value-space universe and supplies
this conclusion by its first projection. This is not a separately quoted
theorem of external literature. The statement asserts no Haar-scaling
interpretation of the determinant modulus.
