# The Siegel parabolic subgroup and the Weyl elements

**GKT §4.4.1**: the Siegel parabolic `P(X)`, (4.4)–(4.6), `M(X)`, `N(X)`, `P(X) = M(X) ⋉ N(X)`
(pp. 114–115); the Weyl elements `w_S` (4.7)–(4.10) (p. 115); **Lemma 4.27** (p. 116).

The module `Langlands.Group.Classical.SiegelParabolic` defines, for a non-degenerate
`ε'`-Hermitian form `h` on a finite-dimensional left module over a division ring with involution,
the Siegel parabolic subgroup of a Lagrangian `X`, its unipotent radical and Levi factors, and the
Weyl elements of a standard basis. Nothing here needs `2` to be invertible (the Levi elements come
from Lemma 4.9 for a polarization, `exists_isometry_extend`, which does not).

## Setting

`h : EpsilonHermitianForm τ ε' V` (the book's `W` is `-ε`-Hermitian, so `ε' = -ε`), `X` a Lagrangian,
`V = X ⊕ Y` a polarization (`IsCompl X Y`, `Y` Lagrangian). Subgroups are subgroups of
`h.isometryGroup : Subgroup (V ≃ₗ[D] V)`.

## Content

- `map_isometryGroup_mul : (g g') X = g (g' X)` (as `Submodule.map`).
- `siegelParabolic h X : Subgroup h.isometryGroup`, the `g` with `g X = X`
  (`mem_siegelParabolic_iff`, `apply_mem_of_mem_siegelParabolic`, `mem_siegelParabolic_of_le`:
  `g X ≤ X` suffices in finite dimension).
- `siegelUnipotent h X : Subgroup h.isometryGroup`, the `g` with `g v - v ∈ X` for all `v` (the book's
  `N(X)`): its elements are the identity on `X` (`apply_eq_of_mem_siegelUnipotent`), it lies in
  `P(X)` (`siegelUnipotent_le_siegelParabolic`), is commutative (`siegelUnipotent_mul_comm`) and
  normal in `P(X)` (`conj_mem_siegelUnipotent`).
- `siegelHerm h X Y : Set (Y →ₗ[D] X)`, the book's `Herm^ε(Y, X)` (4.5), (4.6): the `b` with
  `h(b y, y') + h(y, b y') = 0` for `y, y' ∈ Y` (equivalent to the book's
  `⟨b y, y'⟩ = ε ⟨b y', y⟩^τ` by the `-ε`-Hermitian symmetry of `h`).
- `siegelUnipotentMap hXY b : V →ₗ[D] V`, `v ↦ v + b (v_Y)` (`siegelUnipotentMap_apply`); it is
  isometric for `b ∈ Herm` (`siegelUnipotentMap_map_apply`), giving
  `siegelUnipotentOf h hh hX hXY b hb : h.isometryGroup`, the book's `n(b)`
  (`siegelUnipotentOf_apply`, `siegelUnipotentOf_apply_right : n(b) y = y + b y`,
  `siegelUnipotentOf_mem`), and every element of `N(X)` is an `n(b)`
  (`exists_eq_siegelUnipotentOf`).
- `siegelLevi h X Y = P(X) ∩ P(Y)`; `siegelLeviOf h hh hX hY hXY a` for `a : X ≃ₗ[D] X` is the book's
  `m(a)`: the isometry equal to `a` on `X` with `m(a) Y = Y` (`siegelLeviOf_apply`,
  `map_siegelLeviOf_left`, `map_siegelLeviOf_right`, `siegelLeviOf_mem`), unique
  (`eq_siegelLeviOf`). `restrictOfMemSiegelParabolic hg : X ≃ₗ[D] X` is `p|_X`
  (`restrictOfMemSiegelParabolic_apply`), and
  `exists_eq_siegelLeviOf_mul_siegelUnipotentOf`: every `p ∈ P(X)` is `m(p|_X) n(b)`, the book's
  `p = m(a) n(b)` (`P(X) = M(X) ⋉ N(X)`).
- For a standard basis `e : h.StandardBasis ι` (`Lagrangian.lean`; `X = span {eᵢ}`,
  `Y = span {eᵢ*}`) and `S : Finset ι`: `weylImage`, `weylMap` (`weylMap_basis`,
  `weylMap_map_apply`), and `weylElement e S : h.isometryGroup`, the book's `w_S` (4.8):
  `eᵢ ↦ ε' eᵢ*` and `eᵢ* ↦ eᵢ` for `i ∈ S`, the other basis vectors fixed
  (`weylElement_basis`, `weylElement_fst_of_mem`, `weylElement_fst_of_not_mem`,
  `weylElement_snd_of_mem`, `weylElement_snd_of_not_mem`); for the book's `W`, `ε' = -ε` and this is
  (4.8) verbatim. `isometryGroup_ext`: isometries agreeing on a basis are equal.
- **Lemma 4.27**: `weylElement_mul_weylElement : w_{S₁} w_{S₂} = w_{S₁ ∪ S₂}` for disjoint `S₁, S₂`,
  `weylElement_comm`, and `weylElement_empty : w_∅ = 1`.

## Relation to other files

- The Library's `Langlands.UnitaryGroup.siegelParabolic`, `siegelLevi`, `siegelUnipotent`,
  `weylElement` (`Langlands/Group/Unitary/Hyperbolic.lean`) are the matrix versions for the
  hyperbolic Gram matrix `[[0, 1], [-1, 0]]` over a commutative ring with an involution `c`; its
  `weylElement` is `w_S` for `S = ι` and `ε' = -1`. No comparison theorem is proved here.
- `Langlands.Theta.siegelLeviGroup β` of `Langlands.Theta.Metaplectic.SiegelLevi` is the Levi
  `M(Y)` of the polarization `X × Y` of `polarizedForm β` as pairs `(a, a')`; for `D = F`,
  `τ = id`, `ε' = -1` and `h = ofBilinForm (polarizedForm β)` it corresponds to `siegelLevi h Y X`.
  No comparison theorem is proved here.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.4.1,
  (4.4)–(4.6) and `P(X) = M(X) ⋉ N(X)`, pp. 114–115; (4.7)–(4.10), p. 115; Lemma 4.27 and
  Remark 4.28, p. 116; Lemma 4.9 (existence and uniqueness of `m(a)`), p. 101.

## Declarations

In `Langlands.EpsilonHermitianForm`: `map_isometryGroup_mul`, `siegelParabolic`,
`mem_siegelParabolic_iff`, `apply_mem_of_mem_siegelParabolic`, `mem_siegelParabolic_of_le`,
`siegelUnipotent`, `mem_siegelUnipotent_iff`, `apply_eq_of_mem_siegelUnipotent`,
`siegelUnipotent_le_siegelParabolic`, `siegelUnipotent_mul_comm`, `conj_mem_siegelUnipotent`,
`siegelHerm`, `siegelUnipotentMap`, `siegelUnipotentMap_apply`, `siegelUnipotentMap_map_apply`,
`siegelUnipotentOf`, `siegelUnipotentOf_apply`, `siegelUnipotentOf_apply_right`,
`siegelUnipotentOf_mem`, `exists_eq_siegelUnipotentOf`, `siegelLevi`, `siegelLeviOf`,
`siegelLeviOf_apply`, `map_siegelLeviOf_right`, `map_siegelLeviOf_left`, `siegelLeviOf_mem`,
`eq_siegelLeviOf`, `restrictOfMemSiegelParabolic`, `restrictOfMemSiegelParabolic_apply`,
`exists_eq_siegelLeviOf_mul_siegelUnipotentOf`; in `Langlands.EpsilonHermitianForm.StandardBasis`:
`weylImage`, `weylMap`, `weylMap_basis`, `weylMap_map_apply`, `weylElement`, `weylElement_basis`,
`weylElement_fst_of_mem`, `weylElement_fst_of_not_mem`, `weylElement_snd_of_mem`,
`weylElement_snd_of_not_mem`, `isometryGroup_ext`, `weylElement_mul_weylElement`,
`weylElement_comm`, `weylElement_empty`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.FiveTerm` (and through it the whole
  `EpsilonHermitian` directory).
