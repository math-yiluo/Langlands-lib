# Stalks of Renard's vector sheaf of a nondegenerate target-test module

Helper module for the proof of Renard III.3.1, Proposition
(`Langlands.Sheaf.Renard.CoinvariantStatements.FibreCoinvariantStatement`).
Worker 136 wrote it for Task 5593. It has no new definitions of mathematical
objects. It only describes the ordinary stalk at a point `y` of the published
vector sheaf `ProjectorVectorSheaf.presheaf hY hM` attached to a nondegenerate
module `M` over the pointwise test algebra `PointwiseTestAlgebra.Carrier Y`.

All declarations have prefix `Langlands.Sheaf.Renard.FibreCoinvariantStalk`.
The variables are a type `Y` with `hY : IsLocallyProfinite Y`, a type `M` with a
nondegenerate (`hM : IsNondegenerate`) non-unital module structure over the test
algebra, and a point `y : Y`. As everywhere in this Library family, `M` carries
the complex structure `ProjectorVectorSheaf.originalModule hM`.

## Declarations

- `stalkGerm : M →ₗ[ℂ] stalk y`. It sends `m` to the germ at `y` of Renard's
  global section `(χ_U · m)_U`, that is, of
  `ProjectorVectorSheaf.originalSection hY hM ⊤ m`. It is the composite of
  `originalSection` with Mathlib's `Γgerm y`. `stalkGerm_apply` records this by
  `rfl`.
- `exists_compactOpen_le`: every open neighbourhood `U` of `y` contains a
  compact open `K` (as a `CompactOpen hY`, that is, a basis open of
  `compactOpenBasis hY`) with `y ∈ K`. This is the compact-open neighbourhood
  basis half of `IsLocallyProfinite`.
- `stalkGerm_surjective`. Every element of the stalk is `germ_y s` for some
  section `s` over an open `U ∋ y` (`exists_germ_eq`). Choose a compact open
  `K ∋ y` inside `U` and set `m = s_K`, the `K`-component of the compatible
  family `s`. By `section_ext` and `section_compatible`, the restriction of `s`
  to `K` equals `originalSection K m`. By `originalSection_restrict`, that is the
  restriction of `originalSection ⊤ m`. Hence `germ_y s = stalkGerm m`.
- `stalkGerm_eq_zero_iff`: `stalkGerm m = 0` if and only if there is a compact
  open `K ∋ y` with `action hY M K m = 0`, i.e. `χ_K · m = 0`.
  - Forward: Mathlib's `germ_eq` gives an open `W ∋ y` on which
    `originalSection ⊤ m` restricts to zero. Choose a compact open `K ∋ y`
    inside `W`. The `K`-component of the restricted family is `χ_K · m`, so it
    vanishes.
  - Backward: if `χ_K · m = 0` then every component `χ_W · m`, for compact open
    `W ≤ K`, vanishes, because `χ_W · m = χ_W · (χ_K · m)` (`action_absorb`).
    Hence `originalSection K m = 0` (`section_ext`). Since `originalSection K m`
    is the restriction of `originalSection ⊤ m` (`originalSection_restrict`), its
    germ at `y` is zero.

## Role in the main proof

In `FibreCoinvariantProof`, `M` is the coinvariant module `F_c(X)_G` with its
target-test action, and the stalk is `F′_y`. The two facts here are the
surjectivity of the stalk map and the description of its kernel, which Renard's
proof takes from the Remark of II.2.5 (`F′_y = F′_c(Y)/L″`). This module
re-proves them directly for the stalk of Mathlib's presheaf. It does not use the
published `CompactSectionStalks` statements or the unproved II.2.5 module
comparison.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, III.3.1, Proposition and its proof, printed pp.83–84 /
PDF pp.89–90, and the Remark of II.2.5 cited there. Registered as
`renard-2026-representations-groupes-reductifs-padiques`. The helper lemmas are
internal steps of the implemented proof, not separate results in the source.
