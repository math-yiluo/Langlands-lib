# Continuity of elementary products in coordinates

Module: `Langlands.Algebra.CentralSimple.LandherrContinuity`.

- `continuous_upper_val`, `continuous_lower_val`, `continuous_listProd_ofFn`: over a
  topological ring `R`, the elementary matrices `upper p`, `lower q` and the elementary
  product `listProd (List.ofFn g)` of `L` blocks (module
  `Langlands.Algebra.CentralSimple.LandherrElementary`) depend continuously on their entries
  `g : Fin L → R × R`.
- For a field `k` over `F`, an `F`-algebra `B` with basis `β` and
  `τ : FirstKindInvolution F B`:
  - `targetMap F B τ D g = t D ᵗτ_k(t)` with `t = listProd (List.ofFn g)` in
    `M₂(k ⊗_F B)`;
  - `coordPoint F B β c` is the list of entries
    `(Σᵢ c(j,0,i) (1 ⊗ βᵢ), Σᵢ c(j,1,i) (1 ⊗ βᵢ))` with coordinates
    `c : Fin L × Fin 2 × ι → k`, and `coordOf F B β g` gives the coordinates of entries `g`
    in the basis `1 ⊗ β` of `k ⊗_F B`. The identity `coordPoint_coordOf` recovers `g`
    by applying `coordPoint` to `coordOf g`.
- `exists_coord_nbhd`: let `k` be a complete nontrivially normed field with `2 ≠ 0` and
  `B` finite-dimensional. If `targetMap D g₀ = 1`, then there are neighbourhoods `t α` of the
  coordinates `coordOf g₀ α` such that for all coordinates `c` with `c α ∈ t α` for every
  `α`, the matrix `targetMap D (coordPoint c)` is the square of an element of the
  `k`-subalgebra it generates.

## Proof of `exists_coord_nbhd`

Give `k ⊗_F B` and `M₂(k ⊗_F B)` their module topologies over `k` (`moduleTopology`), for
which they are topological rings and every `k`-linear map between finite-dimensional spaces
is continuous. `exists_isOpen_mul_self_eq` (module
`Langlands.Algebra.CentralSimple.LandherrSquareRoot`) gives an open set `U` of coordinates
around those of `1` (in a `k`-basis of `M₂(k ⊗_F B)`) consisting of squares in the generated
subalgebras. The map `c ↦ targetMap D (coordPoint c)` is continuous (products,
`τ_k` is `k`-linear, coordinates are linear), so the preimage of `U` is a neighbourhood of
`coordOf g₀`; a neighbourhood in the product topology contains a box of neighbourhoods
(`Filter.mem_pi'`).

## Provenance

Elementary topology: the local condition "`t diag(y, 1) ᵗτ(t)` is close to `1`, hence a
square" is open in the entries of `t`. In the proof of Landherr's theorem this lets global
approximations of the local elementary products satisfy the local square condition.
