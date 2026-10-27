# Proof of the full determinant modulus under ordered refinement coordinates

`Langlands.Parabolic.refinementCoordinatesModulus` proves the exact closed
proposition `Langlands.Parabolic.RefinementCoordinatesModulusTheorem.{uF}`
from `Langlands.Representation.Parabolic.RefinementCoordinatesModulusStatement`.
The theorem's type is that statement constant itself.

For every natural prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`, natural rank `n`, block shapes `B D` of `n`,
a refinement `S` of `D`, and coordinate data `e`, `hs` and `hc` as in the
statement, it proves
`RefinementCoordinatesNormalization.ModulusClause F T B D S e hs`. That is,
for every `m : B.Levi F.Carrier`, the composed full modulus at the concrete
Levi refinement coordinates of `m` equals `T.leviModulus B m` in `ℝ≥0ˣ`.

The proof introduces the inputs of the closed statement. It then applies the
published helper
`Langlands.Parabolic.RefinementCoordinatesNormalization.modulus_of_coordinates`
from `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof`.
That helper takes exactly these arguments, including the coordinate identity
`hc`, and concludes the same `ModulusClause`. The parent proof
`Langlands.Parabolic.refinementCoordinatesNormalization` uses it for the first
conjunct of its combined target.

The helper is where the mathematics is done. It uses `hc` to identify `B`
with `D.flatten S` and `e` with the canonical flattened block equivalence. It
then identifies the concrete Levi equivalence with `flattenedLeviEquiv` and
applies `PadicField.TopologicalData.composedLeviModulus_flattened` from
`Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`,
which is the determinant-product calculation. This module repeats neither the
coordinate transport nor that calculation.

No hypothesis is added to the statement. The proof has no modulus premise,
supplied equivalence, separate order assumption, positive-rank, nonempty-family
or smoothness hypothesis. Rank zero and empty block families are included.
The conclusion is the determinant-character equality only; it says nothing
about Haar scaling.

This is an internal derivation from published Library results; it cites no
external literature directly.
