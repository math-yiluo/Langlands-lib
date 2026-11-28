# Strong approximation for a number field away from one finite place

Module: `Langlands.Algebra.CentralSimple.LandherrStrongApprox`.

Let `F` be a number field.

- `exists_small_mem_latticeIdeal`: for a finitely supported divisor `m₀` on the finite
  places, a finite place `v₀` and `δ > 0`, there is `θ ≠ 0` in `F` with
  `v(θ) ≤ exp(m₀ v)` at every finite `v ≠ v₀` and `|θ|_w < δ` at every infinite place `w`.
- `exists_strongApprox`: given a finite set `S` of finite places, points `c v ∈ F_v` with
  neighbourhoods `U v` for `v ∈ S`, points `b w ∈ F_w` with neighbourhoods `W w` at all
  infinite places, and a finite place `v₀ ∉ S`, there is `x ∈ F` with `x ∈ U v` for `v ∈ S`,
  `x ∈ W w` for all infinite `w`, and `v(x) ≤ 1` at every finite `v ∉ S ∪ {v₀}`.

## Proofs

`exists_small_mem_latticeIdeal`: let `I` be the fractional ideal (`latticeIdeal`, module
`Langlands.Global.Hecke.AdelicLattice`) of the divisor `m₀ + k v₀`. Its absolute norm is
`A₀ N(v₀)^(-k)`, which is small for `k` large, so Minkowski's convex body theorem
(`exists_ne_zero_mem_ideal_lt` with `convexBodyLT`) gives a nonzero `θ ∈ I` with
`|θ|_w < δ` at all infinite places; membership in `I` gives the bounds at `v ≠ v₀`.

`exists_strongApprox`: choose lattice levels `n v` such that the additive lattices of level
`n v` around `c v` lie in `U v`, and radii `ε w` with balls around `b w` inside `W w`. Finite
approximation (`exists_approx`, module `Langlands.Global.Hecke.AdelicLattice`) gives `x₁ ∈ F`
close to `c v` at `v ∈ S` and integral at all other finite places. Let `C w ≥ 0` bound the
archimedean fundamental set `Global.archimedeanFundamentalSet F` (compact,
`Global.isCompact_archimedeanFundamentalSet`), and let `θ` be as above for `m₀ = Σ n v · v`
and `δ = min_w ε w / (C w + 1)`. Write `θ⁻¹ (b - x₁)` at the infinite places as an integer
`a ∈ 𝓞_F` plus an element of the fundamental set
(`Global.exists_sub_integer_mem_archimedeanFundamentalSet`). Then `x = x₁ + θ a` works: at
`v ∈ S`, `θ a` lies in the lattice of level `n v`; at infinite `w`,
`|x - b w|_w = |θ|_w · |θ⁻¹(b w - x₁) - a|_w ≤ δ C w < ε w`; at finite `v ∉ S ∪ {v₀}`, `x₁`,
`θ` and `a` are integral.

## Provenance

The strong approximation theorem for the additive group of a number field with respect to
the set of places omitting one finite place, proved here directly from Minkowski's
theorem. In
the proof of Landherr's theorem it is applied coordinatewise to approximate local elementary
matrices by global ones that are integral away from a finite set and one split place.
