# Jacquet–Cartan data from standard parabolic systems

Module `Langlands.Representation.Aubert.General.JacquetCartanAssembly`.

This module reduces the construction of a `Langlands.JacquetCartanDatum` (module
`Langlands.Representation.Smooth.Admissibility.JacquetCartan`) to structural
facts about the standard parabolic subgroups of a reductive group. It contains
no facts about actual reductive groups. It is the formal part of the realization
suggested for `Langlands.Aubert.General.RationalPointsJacquetCartanDatumStatement`
in the Markdown of that statement. The source is D. Renard, *Représentations des
groupes réductifs p-adiques* (French version dated 9 July 2026, source id
`renard-2026-representations-groupes-reductifs-padiques`), V.5.1, V.5.2 and
VI.2.1.

## `Langlands.Aubert.General.HasWallContraction`

`HasWallContraction levi unipotent cartanSet I` is a property of subgroup
families `levi`, `unipotent : Finset Δ → Subgroup G`, a family of sets
`cartanSet : Finset Δ → Set G`, and a finite set `I` of simple roots. It says the
following. Let `O` be a neighbourhood of `1`. For each proper subset `J ⊊ I`, let
`S J` be a finite subset of `N_J ∩ M_I`. Then there is a compact set `D` such
that every `t ∈ cartanSet I` satisfies one of two alternatives:

- `t = d * z` with `d ∈ D`, `z ∈ M_I`, and `z` commuting with every element of
  `M_I`;
- for some `J ⊊ I`, `t * u * t⁻¹ ∈ O` for every `u ∈ S J`.

This has the same shape as the `contraction` field of `JacquetCartanDatum`, with
walls the proper subsets `J ⊊ I` and wall subgroups `N_J ∩ M_I`. It is the
dichotomy used in the proof of Renard VI.2.1 `a) ⇒ b)` (printed pp. 138–139).
There, dominant elements either stay in a compact set modulo the centre, or some
`|α(t)|` tends to `0` (VI.2.1.1), and then `t` contracts the unipotent radical of
the maximal standard parabolic subgroup `P_α` (V.5.2 (iii), printed p. 123). Here
every proper standard parabolic subgroup of `M_I` is a wall, not only the
maximal ones. With these walls the dichotomy follows from lattice data (see
`Langlands.Representation.Aubert.General.CartanLatticeContraction`).

## `Langlands.Aubert.General.StandardParabolicSystem`

`StandardParabolicSystem G`, for a group `G` with a topology, consists of the
following data and properties.

- A type `Δ` of simple roots with decidable equality.
- Subgroup families `parabolic`, `levi` and `unipotent` on `Finset Δ`. They model
  the standard parabolic subgroup `P_I`, its standard Levi subgroup `M_I` and its
  unipotent radical `N_I`.
- `parabolic_mono`: `I ⊆ J` implies `P_I ≤ P_J`.
- `levi_mul_unipotent`: every `p ∈ P_I` is `m * n` with `m ∈ M_I` and `n ∈ N_I`.
- `levi_le_normalizer`: `M_I` normalizes `N_I`.
- `isClosed_levi`: `M_I` is closed.
- `top` with `unipotent_top : N_top = ⊥`. For a reductive group this is the
  finite set of all simple roots.
- `unipotent_descent`: for `J ⊆ I`, every `n ∈ N_J` is `u * n'` with
  `u ∈ N_J ∩ M_I` and `n' ∈ N_I`. This is the decomposition
  `N_J = (N_J ∩ M_I) N_I`.
- `iwasawa`: `G = P_∅ K` for a compact set `K` (Renard V.5.1 (1), with `K = K₀`).
- `cartanCompact I`, `cartanSet I`: a compact set `K_I ⊆ M_I` and a countable set
  `Λ_I ⊆ M_I` with `cartan : M_I = K_I Λ_I K_I` (Renard V.5.1 (4), (5), with
  `K_I = K₀ ∩ M_I` and `Λ_I` the dominant representatives `C̃⁺`, notation V.3.23).
- `contraction`: `HasWallContraction levi unipotent cartanSet I` for every `I`.

## Declarations

- `StandardParabolicSystem.wallUnipotent 𝒮 I J`: the wall subgroup
  `N_J ⊓ M_I` of a wall `J ⊊ I`.
- `StandardParabolicSystem.toJacquetCartanDatum 𝒮 : JacquetCartanDatum G`, the
  assembled datum.
- `StandardParabolicSystem.nonempty_jacquetCartanDatum`: a standard parabolic
  system yields `Nonempty (JacquetCartanDatum G)`.

## The construction and its proofs

`toJacquetCartanDatum` uses the following fields.

- Indices: `Finset Δ`, with rank `I.card` and top index `top`. Levi and unipotent
  subgroups are `levi` and `unipotent`, so `unipotent_top`, `levi_le_normalizer`
  and `isClosed_levi` carry over directly.
- Iwasawa: for every index `I`, the compact set is the `K` of `iwasawa`. Write
  `g = p * k` with `p ∈ P_∅`. Then `p ∈ P_I` by `parabolic_mono`, so
  `p = m * n` with `m ∈ M_I` and `n ∈ N_I` by `levi_mul_unipotent`, and
  `g = m * n * k`.
- Walls: the walls of `I` form the subtype `{J : Finset Δ // J ⊂ I}`. The wall
  subgroup is `wallUnipotent`, which lies in `M_I` by `inf_le_right`. The
  descent index of `J` is `J` itself. Its cardinality is smaller
  (`Finset.card_lt_card`), and `unipotent_descent` for `J ⊆ I` is exactly the
  required factorization.
- Cartan: the fields `cartanCompact`, `cartanSet` and their properties carry over
  directly.
- Contraction: the field `contraction`, since `HasWallContraction` is the
  `contraction` condition of the datum for these walls.

## What remains for the target statement

To prove `RationalPointsJacquetCartanDatumStatement`, one needs a
`StandardParabolicSystem` on `G(F) = RationalPoint F G.X`, with the point
topology, for every connected reductive `G` over a nonarchimedean local field
`F`. Its `Δ` must lie in the universe of `F`. Candidates are the actual standard
subgroups `Langlands.Aubert.General.RationalPointFamily.parabolic`, `levi` and
`unipotent`, indexed by finite sets of `SimpleRoot i ν` for a maximal split torus.
The field `contraction` follows from a lattice model of the Cartan elements by
`IsCartanLatticeModel.hasWallContraction` (module
`Langlands.Representation.Aubert.General.CartanLatticeContraction`); the module
`Langlands.Representation.Aubert.General.RationalCartanLatticeModel` checks the
lattice model for `G(F)` under explicit hypotheses. The remaining inputs are the
Borel–Tits structure of the standard parabolics, the Iwasawa and Cartan
decompositions (Renard V.5.1), and the contraction estimate V.5.2 (iii). This
module does not prove these.
