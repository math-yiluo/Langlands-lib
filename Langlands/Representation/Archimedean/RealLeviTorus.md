# Torus integrals, block orthogonal invariance and growth bounds along `N̄_Q`

Lean module: `Langlands.Representation.Archimedean.RealLeviTorus`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It
is internal measure-theoretic infrastructure for the limit argument along the standard parabolic
subgroup `Q` (module `RealLeviLimit`). The module has no `Prop`-valued statement. It only proves
lemmas. No literature statement is claimed, and nothing here is cited from a source. Unprefixed
names below are in the namespace `Langlands.Archimedean.RealLeviTorus`.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`.
These come from earlier modules:

* `Slot N`, `coeffs`, `zeroModes` (modules `RealInducedBlockBound`, `RealInducedTorusCore`).
  For a list of slots `L = [s_0, …, s_{r−1}]` at the positions `p_0, …, p_{r−1}`, `coeffs L F g`
  is defined by recursion on the list: `coeffs [] F g = F g`, and
  `coeffs (s :: rest) F g = blockFourierCoefficient N s.p s.j (coeffs rest F) g`.
  The Library's `blockFourierCoefficient N p k f g` is
  `∫_0^{2π} e^{−ikθ} f(r_p(θ) g) dθ`, where `r_p(θ) = blockRotation N p θ` is the rotation in
  the coordinates `p, p + 1`. `zeroModes L` sets all modes to `0`.
* The block data of `Q` (module `RealLeviChartIntegralStatement`): `c` blocks of sizes
  `sz : Fin c → ℕ`, `N = ∑ i, sz i`, `cls sz p` the block of the position `p`, `Coord sz` the
  coordinates of `N̄_Q`, `lower sz X = n̄(X)` and `lowerGL sz X`.
* `blockDiagHom sz` and `blockDiagGL sz` (block diagonal matrices) and `haarK` (the Haar
  probability measure on `O(n)`), from the module `RealLeviParabolicIntegrationStatement` and the
  Library's `RealPrincipalSeriesDuality`.
* `BlockZero`, `blockOrth sz` (the orthogonal matrices without entries between different blocks),
  `adCoord k X` (the coordinates of `k n̄(X) kᵀ`) and `measurePreserving_adCoord`, from the module
  `RealLeviGeometry`.
* `GramFormula.gram l M`, the Gram determinant of the rows `l, …, N − 1` of `M` (Library module
  `PrincipalSeriesGramFormula`).

## Results

**Torus parameters** (section `Torus`).

* `torusElem L θ` for `θ : Fin L.length → ℝ`: `torusElem [] θ = 1` and
  `torusElem (s :: rest) θ = torusElem rest (θ ∘ succ) * r_{s.p}(θ_0)`, so
  `torusElem L θ = r_{p_{r−1}}(θ_{r−1}) ⋯ r_{p_0}(θ_0)`. It is continuous
  (`continuous_torusElem`) and lies in `O(N)` (`torusElem_mem_unitaryCompact`).
* `torusMeasure r`: the product measure `Measure.pi` of `r` copies of Lebesgue measure restricted
  to `(0, 2π]`. It is finite (instance `isFiniteMeasure_torusMeasure`).
* `exists_bound_mul`: a continuous `F` is bounded on `O(N) g`.
* `integrable_torus`: `θ ↦ F(torusElem L θ * g)` is integrable for continuous `F`.
* `coeffs_eq_integral`: for continuous `F`, every list `L` and every `g`,
  `coeffs (zeroModes L) F g = ∫ F(torusElem L θ * g) d(torusMeasure L.length)(θ)`.

**Torus elements of tied slots** (section `TorusOrth`). `torusElem_mem_blockOrth`: if every slot
`s ∈ L` has `cls sz s.p = cls sz (s.p + 1)`, then `torusElem L θ ∈ blockOrth sz` for every `θ`.

**Block orthogonal elements are block diagonal** (section `BlockDiag`).

* `diagBlock g i`: the diagonal block `i` of an `N × N` matrix, i.e. the entries
  `g (pos sz i a) (pos sz i b)`.
* `blockDiagHom_diagBlock`: `blockDiagHom sz (diagBlock g) = g` if `BlockZero sz g`.
* `blockDiagHom_injective`.
* `diagBlock_mul_transpose`: the diagonal blocks of an orthogonal `g` with `BlockZero sz g` are
  orthogonal.
* `orthBlock hg i`: the diagonal block `i` of `g ∈ blockOrth sz`, as an element of `O(sz_i)`.
  `blockDiagGL_orthBlock`: `blockDiagGL sz (orthBlock hg) = g`.

**Invariance of the integral over `K_M`** (section `Invariance`). Let `K_M = ∏_i O(sz_i)` carry
the product `Measure.pi (fun i => haarK (sz i))`.

* `blockDiagGL_mul`: `κ ↦ blockDiagGL sz κ` is multiplicative on `K_M`.
* `integral_blockOrth_mul`: for `g ∈ blockOrth sz` and every `f : GL_N(ℝ) → E` (`E` a real
  normed space), `∫_{K_M} f(g · diag(κ)) dκ = ∫_{K_M} f(diag(κ)) dκ`, where
  `diag(κ) = blockDiagGL sz κ`.

**Substitution by `Ad(g)`** (section `Subst`). For `g ∈ blockOrth sz`:

* `adCoord_adCoord_inv`: `Ad(g⁻¹) (Ad(g) X) = X`.
* `continuous_adCoord`: `Ad(k)` is continuous for every matrix `k`.
* `adHomeomorph hg`: `Ad(g)` as a homeomorphism of `Coord sz → ℝ`, with inverse `Ad(g⁻¹)`.
* `integral_adCoord`: `∫ f(Ad(g) X) dX = ∫ f(X) dX` for every `f` with values in a real normed
  space. `lintegral_adCoord`: the same for `ENNReal`-valued lower integrals.

**Growth bounds** (section `Growth`).

* `gram_zero_eq`: `G_0(M) = (det M)²`.
* `norm_le_gram_fin`: suppose `F(diag(a) u g) = c(a) F(g)` for all `a : Fin N → ℝˣ`, all `u` in
  the upper unipotent subgroup and all `g`, where `‖c(a)‖ = ∏_l |a_l|^{σ_l}`. Suppose
  `‖F(k)‖ ≤ C` on `O(N)`. Then for every `y` with `G_0(y) = 1`, every `κ ∈ O(N)` and every
  `ε : Fin N → ℝ` with `ε_l = (σ_l − σ_{l−1})/2` for `l ≥ 1`,
  `‖F(y κ)‖ ≤ C ∏_l G_l(y)^{ε_l}`. The value `ε_0` is arbitrary, because `G_0(y) = 1`.

## Proof

`coeffs_eq_integral` is proved by induction on the list. For the empty list, the measure on
`Fin 0 → ℝ` is a Dirac measure (`Measure.pi_of_empty`). For `s :: rest`, unfolding `coeffs` with
mode `0` gives `∫_0^{2π} coeffs (zeroModes rest) F (r_{s.p}(a) g) da`. The induction hypothesis
rewrites the inner coefficient as an integral over `torusMeasure rest.length`. The two integrals
are combined into one integral over the product measure (`integral_prod`). The integrand is
continuous and bounded by the bound of `exists_bound_mul`, so it is integrable. Mathlib's
measure-preserving equivalence `MeasurableEquiv.piFinSuccAbove` at `0` identifies the product with
`torusMeasure (rest.length + 1)` (`measurePreserving_piFinSuccAbove`). The definition of
`torusElem` matches this splitting of `θ`.

`torusElem_mem_blockOrth` is an induction using `blockRotation_mem_blockOrth` and the closure of
`blockOrth sz` under products (it is a subgroup, module `RealLeviGeometry`).

`blockDiagHom_diagBlock` is checked entrywise via the block positions `pos sz i a`
(`pos_cls`): equal blocks give the diagonal block entry (`blockDiagHom_pos_pos_self`), and
different blocks give `0` on both sides (`blockDiagHom_pos_pos_of_ne` and `BlockZero`).
Injectivity is the same computation. `diagBlock_mul_transpose` applies the injectivity to
`blockDiagHom sz (diagBlock g · (diagBlock g)ᵀ) = g gᵀ = 1`, using that `blockDiagHom sz` is
multiplicative and commutes with transposition (`blockDiagHom_transpose`).

`integral_blockOrth_mul` writes `g = diag(ρ)` with `ρ = orthBlock hg ∈ K_M` and uses the left
invariance of the Haar measure on the compact group `K_M` (`integral_mul_left_eq_self`; the
product of the Haar probability measures is a left invariant measure on the product group).

`adCoord_adCoord_inv` uses `lower_adCoord` (`n̄(Ad(k) X) = k n̄(X) kᵀ`), `g⁻¹ = gᵀ` and
`gᵀ g = 1`, and then `lower_injective`. Continuity of `Ad(k)` follows from the continuity of
matrix products and of `lower sz`. `integral_adCoord` and `lintegral_adCoord` combine
`measurePreserving_adCoord` with the measurable embedding of the homeomorphism `adHomeomorph`.

`gram_zero_eq`: `paddedGram 0 M = M Mᵀ`, so `G_0(M) = det(M Mᵀ) = (det M)²`.
`norm_le_gram_fin` is `RealBlockChart.norm_le_gram` (module `RealBlockChartBound`) for `N = m + 1`, after splitting off the factor `l = 0`
(`Fin.prod_univ_succ`), where `G_0(y) = 1`. For `N = 0` the group is trivial, the product is
empty and the bound is `‖F(κ)‖ ≤ C`.

## Use

In `RealLeviLimit`, `coeffs_eq_integral` turns the torus coefficient of the statement into an
integral that can be exchanged with the integrals over `K_M` and `N̄_Q`.
`torusElem_mem_blockOrth`, `integral_blockOrth_mul` and `integral_adCoord` move the torus elements
of the induction blocks of `ds` (which lie inside the blocks of `Q`) past `n̄(X)` and absorb them
into `K_M`. `norm_le_gram_fin` bounds principal-series functions along `n̄(Y) κ` by products of
Gram determinants.

The diagonal-block decomposition and `gram_zero_eq` are imported from `RealLeviBlockDecomposition`.
