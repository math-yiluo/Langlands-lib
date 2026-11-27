# Cutting a section off to the open cell at finitely many places

Module `Langlands.Global.Factors.CuspidalPairEisensteinSemilocalCutoff`, namespace
`Langlands.Global.CuspidalPairEisenstein.SemilocalCutoff`.

Fix a finite set `S₀` of finite places and `ε : ∀ v, F_v` with `ε_v ≠ 0` and `|ε_v|_v ≤ 1`
for `v ∈ S₀` (written `hε`). The module defines the cutoff `β = cutoff r t S₀ ε` on
`GL_(r+t+2)(𝔸)` and proves that multiplying a section by `β` keeps the section conditions
of [CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) and
multiplies the open-cell integrand by `β(w u'(Y))`. The local algebra is in
[CuspidalPairEisensteinOpenCellCutoff.md](CuspidalPairEisensteinOpenCellCutoff.md).

## Content

Topology of a valued field `K` (with `Valued K Γ₀`):

- `isOpen_lt_valuation a`: the ball `{x | |x| < |a|}` is open.
- `exists_ball_subset`: every neighbourhood of `0` contains a ball `{x | |x| < |a|}` with
  `a ≠ 0` and `|a| ≤ 1`; `exists_ball_subset_pi` and `exists_matrix_ball_subset` give the
  same for finite products and for matrix spaces, with one common `a` for all coordinates.

The cutoff:

- `parabolic_lowerZero`: an element of the upper two-block parabolic
  `(blockShape r t).parabolic R` has vanishing lower left `(t + 1) × (r + 1)` block.
- `InCellAt r t S₀ ε g`: for every `v ∈ S₀` the component `g_v` (`Oneplace.comp`) satisfies
  `InCell` for the valuation of `F_v` and the level `|ε_v|_v`.
- `cutoff r t S₀ ε g`: `1` if `InCellAt r t S₀ ε g`, else `0`.
- `stab r t S₀ ε`: the subgroup of `k` with `InCellAt (g k) ↔ InCellAt g` for all `g`;
  `cutoff_mul_stab`: `β(gk) = β(g)` for `k` in it.
- `congruenceSet v n ε`: the local matrices `x` with `x - 1` and `x⁻¹ - 1` of entries of
  valuation `< |ε|`; it is open (`isOpen_congruenceSet`) and contains `1`;
  `inCell_mul_iff_of_mem`: right multiplication by its elements preserves `InCell` in both
  directions (`InCell.mul_right` for `x` and for `x⁻¹`).
- `isOpen_stab hε`: `stab` is open, since it contains the neighbourhood of `1` of matrices
  whose components at the places of `S₀` lie in the congruence sets; `openStab hε` is the
  open subgroup.
- `cutoff_mul_left`: `β(pg) = β(g)` for `p ∈ P(𝔸)` (`inCell_mul_left_iff`).
- `inCellAt_openCell_iff`: `InCellAt (w u'(Y))` holds exactly when
  `|(Y_v)_(ij)|_v < |ε_v|_v` for every `v ∈ S₀` and all entries
  (`inCell_openCellMatrix_iff`, with `comp_openCellWeyl` and `comp_openCellUnipotent`).
- `cutoff_mul_adelicAt`: `β` is right invariant under matrices placed at a finite place
  `v ∉ S₀`; `cutoff_pair`: `β` does not depend on the archimedean component.

Sections:

- `leviEmbedding_mem_parabolic`, `unipotent_mem_parabolic`: the Levi and the unipotent
  radical of `P(𝔸)` lie in `P(𝔸)`.
- `finite_range_cutoff_translate hε`: the right translates `g ↦ β(gk)`,
  `k ∈ standardCompact F (r+t+2)`, form a finite set. The open subgroup `stab ∩ K` has
  finite index in the compact group `K` (`Subgroup.quotient_finite_of_isOpen`), and the
  translate depends only on the coset.
- `slice_cutoff_mul_mem`: the normalized Levi slice `m ↦ δ_P(m)^(-1/2) (βφ)(m k)` is
  `β(k)` times that of `φ`, so it lies in every submodule containing that of `φ`.
- **`isSection_cutoff_mul hε`**: if `IsSection T T' φ`, then
  `IsSection T T' (fun g => β g * φ g)`. Smoothness: on `a ↦ (a, b)` the function is the
  constant `β(1, b)` times that of `φ` (`cutoff_pair`). Right invariance: under
  `J ⊓ (openStab hε).comap ofFinite`, for the open subgroup `J` of `φ`. `K`-finiteness: the
  span of the translates `(βφ)(· k)` lies in the finite sum, over the finitely many
  translates `b` of `β`, of the images of the span of the translates of `φ` under
  multiplication by `b`. Left invariance under the unipotent radical: `cutoff_mul_left`.
  Levi slices: `slice_cutoff_mul_mem`.
- **`isSphericalSectionOutside_cutoff_mul`**: if `S₁ ⊆ S₀` and
  `IsSphericalSectionOutside T T' S₁ φ`, then
  `IsSphericalSectionOutside T T' S₀ (fun g => β g * φ g)`: for `v ∉ S₀` both factors are
  invariant under `GL(𝒪_v)` at `v` (`cutoff_mul_adelicAt`), and cusp forms spherical
  outside `S₁` are spherical outside `S₀`.

The integrand:

- `generalLinearWhittakerFunction_const_mul`: the global Whittaker coefficient is linear in
  a constant factor (`integral_const_mul`).
- `leviWhittaker_cutoff_mul`: `W_M(βf)(h) = β(h) W_M(f)(h)`, since `β` is invariant under
  the Levi translations `diag(x, y)` in the definition of `leviWhittaker`.
- **`openCellIntegrand_cutoff_mul`**:
  `openCellIntegrand ψ (fun g => β g * φ g) s Y = β(w u'(Y)) · openCellIntegrand ψ φ s Y`.

## Provenance

In the proof of Shahidi (1981), Theorem 5.1, pp. 351–352 (`shahidi-1981-certain-l`), the
local data at the finite places of the finite set `S` are chosen with nonzero local value by
Proposition 3.1 (p. 332). The Library instead multiplies the section by the indicator `β`
which, at each of these places, requires the open-cell coordinate `y` of `g_v = p w u'(y)` to
lie in a small ball around `0`: a neighbourhood of the coset `P w` in the open chart
`P w U'` of `P \ G`, corresponding to `u'(0) = 1` in `U'`. The integrand over these places
is then an indicator. The definitions and the lemmas of this module
are internal to the Library.
