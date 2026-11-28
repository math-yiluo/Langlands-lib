# Charts of the square of an abelian scheme

Module `Langlands.AbelianScheme.ArtinianSquareCharts` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

Let `B` be an abelian scheme over `Spec R` in the setting of `ArtinianConstantCharts`.

- `CSGrp` is the base change of the constant group scheme `C` to `Spec R`. The projection
  `ρ : CS ⟶ A₀` and the constant section `τ : A₀ ⟶ CS` are multiplicative (`isMulMap_ρ`,
  `isMulMap_τ`, in the sense of `IsMulMap` of `GroupSchemeShear`). For `τ` this follows from
  `ρ ∘ τ = id` and the pullback description of `CS` with projections `ρ` and the structure map.
- `modelB₂` is the square of the constant model (`Model.prod`, module `ArtinianChartProducts`),
  and `jB₂` the square of the inclusion of the special fibre into `B × B`.
- `shearAut` is the automorphism `(x, y) ↦ (x y, y)` (`shear`, module `GroupSchemeShear`) of the
  squares of `C`, of its base change, of `A₀` and of `B`, as a `Model.Aut` (module
  `ArtinianChartOperations`). Its compatibilities hold because the base-change maps `C_R ⟶ C`,
  `τ` and `jB` are multiplicative.
- For a family of charts `K` of `B`, `Charts.prodFamily` is the product chart family of `B × B`
  and `Charts.squareFamily` its union with the conjugate of the product family by the shear.
  The opens of the conjugate are inverse images of the product opens under the shear.
  For `R` local Artinian and given lifts `D` of the transition maps of `K`,
  `Charts.prodLifts` gives the product lifts. When `R'` is also Artinian,
  `Charts.squareLifts` combines these with their conjugates by the shear, using `Lifts.sum`
  to choose lifts across the two parts.

## Provenance

The comparison of product charts with the pullback by `(x, y) ↦ (x + y, y)` follows the
product and automorphism argument of Kai-Wen Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, Harvard thesis revised 14 March 2021, proof of Proposition 2.2.4.1 (printed
pp. 152–154, PDF pp. 180–182). Putting both families in a single cover lets the proof compute
one obstruction cocycle on both.
