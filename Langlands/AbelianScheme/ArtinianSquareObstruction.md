# The obstruction on the square of an abelian scheme

Module `Langlands.AbelianScheme.ArtinianSquareObstruction` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

Assume `R'` Artinian and `R` local Artinian. Let `K` be a family of charts of an abelian scheme
`B` over `Spec R` and `D` lifts of its transition maps to the constant abelian scheme `C` (module
`ArtinianAbelianCharts`). For the obstruction statements assume moreover
`maximalIdeal R' * ker φ = 0`, fix difference coordinates `b` for the target of `C` and the ideal
`ker φ`, let `F` be a reduction of `C` modulo the maximal ideal of `R'` and `F.fibreProduct F` the
induced reduction of `C × C`. The lifts `Charts.squareLifts D` on the charts of `C × C` (module
`ArtinianSquareCharts`) are observed through the first projection `fst : C × C ⟶ C`.

- On a triple overlap of product charts (indices `inl a`, `inl c`, `inl e`), `obstruction_inl`
  identifies the obstruction of the square with the pullback, along the reduction of `fst`, of
  the obstruction of `D` at the first components `(a.1, c.1, e.1)`.
- For the product lifts, `prodObstruction_fst` and `prodObstruction_snd` identify the obstruction
  through each projection with the pullback along its reduction of the obstruction of `D` at
  the corresponding index components.
- On a triple overlap of sheared product charts, `obstruction_inr` identifies the obstruction
  through `fst` with the pullback along the reduction of the shear of the first product
  obstruction minus the second.

## Proof

The product lifts are products of the lifts `D` (`Lifts.prod_θ_fst`, `Lifts.prod_θ_snd`), so
`obstruction_comap` (module `TransitionObstructionComap`) applies with the projections. The
sheared lifts are conjugates `σ⁻¹ ∘ θ ∘ σ` by the shear `σ` (`squareθ_inr`), so `obstruction_comap`
along `σ` relates them to the product lifts observed through `σ⁻¹ ≫ fst = fst / snd`, and
`obstruction_mul_inv` splits that observer, since `C` is commutative.

## Provenance

Kai-Wen Lan's proof of Proposition 2.2.4.1 compares the obstruction on product charts of `A × A`
with its transport by `(x, y) ↦ (x + y, y)` (*Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, printed pp. 152–154, PDF pp. 180–182).
The Lean comparison takes the first component by postcomposing with `fst`. For the conjugated
lifts, the inverse shear turns that observer into `fst / snd`, giving the subtraction above.
