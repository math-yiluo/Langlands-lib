# The superdiagonal filtration of the upper unitriangular group

This module is elementary matrix algebra over a commutative ring `A`. It
supports the proof of Milne 2017, Theorem 16.26(a), in
`Absolute/TriangularSplitExtension`. It sets up the filtration of the upper
unitriangular group `U_N(A)` by superdiagonals. It also gives a calculus for
working in that filtration modulo an arbitrary subgroup `𝒰`. Everything is in
the namespace `Langlands.GroupScheme.TriangularLayer`, and matrices are indexed
by `Fin N`.

## Matrices

- `IsUpper X`: `X i j = 0` whenever `j < i`.
- `IsLevel a X`: `X i j = 0` whenever `j ≤ i + a`. So `IsLevel 0` means
  strictly upper triangular, and `IsLevel N X` forces `X = 0`
  (`isLevel_top`).
- Closure lemmas: `IsUpper.add`, `IsUpper.mul`, `IsLevel.add/neg/sub/mono`,
  `IsLevel.mul_isUpper`, `IsUpper.mul_isLevel`, `IsLevel.mul` (levels add
  plus one), and `IsUpper.map`, `IsLevel.map` for ring maps.
  `IsUpper.mul_apply_self` computes the diagonal of a product of upper
  triangular matrices.

## Layers and scaling

- `layer a : Matrix →+ Matrix` keeps the entries on the `(a + 1)`-st
  superdiagonal (`j = i + a + 1`) and replaces all other entries by zero.
  Lemmas: `layer_apply`, `layer_layer`, `layer_map`,
  `IsLevel.layer_eq_zero`, `IsLevel.succ_of_layer_eq_zero` (a level-`a`
  matrix with zero layer has level `a + 1`).
- `scale c b : Matrix →+ Matrix` multiplies the entry at `(i, j)` by
  `c i i * _ * b j j`. `scale_layer`, `scale_eq_self`, `scale_map` and
  `scale_congr` give its basic behaviour. `layer_mul_mul` says that for
  upper triangular `c, b` and level-`a` `X`, the layer of `c * X * b` is
  `scale c b` applied to the layer of `X`.

## The filtration

- `upper A N` is the subgroup of upper triangular invertible matrices. It is
  defined as the published block parabolic subgroup
  `GeneralLinear.blockParabolicSubgroup A (fun i => -i)`, and `mem_upper`
  identifies it with `IsUpper`.
- `W A N a` is the subgroup of `g` with `IsLevel a (g - 1)`. `W A N 0` is the
  upper unitriangular group. The terms decrease (`W_anti`), and `W A N N`
  is trivial (`eq_one_of_mem_W_top`).
- `W_conj`: `W a` is normalized by `upper`. `map_mem_W` says ring maps
  preserve `W a`.
- `layer_mul`, `layer_inv`: on `W a`, `g ↦ layer a (g - 1)` is a group
  homomorphism to the additive group of matrices. `mem_W_succ`: its kernel
  is `W (a + 1)`. `layer_conj` computes the layer of a conjugate by an
  upper triangular matrix through `scale`. `scale_of_mem_W` says that
  conjugation by a unitriangular matrix acts trivially on layers.

## Layers modulo a subgroup

Fix a subgroup `𝒰` of `GL_N(A)`.

- `layerGroup 𝒰 a` is the additive subgroup of layers `layer a (w - 1)` of
  the elements `w ∈ 𝒰 ∩ W a`.
- `Approx 𝒰 a g` says that `g ∈ 𝒰 · W a`. `approx_of_mem_W` covers
  `g ∈ W a`, and `mem_of_approx_top` gives `g ∈ 𝒰` from `Approx 𝒰 N g`.
- `Rel 𝒰 a g V` says that `g = u * w` with `u ∈ 𝒰` and `w ∈ W a`, and that
  the layer of `w - 1` agrees with the layer of `V` modulo `layerGroup 𝒰 a`.
  The calculus is as follows.
  - `Approx.rel` and `Rel.approx` convert between the two notions.
  - `rel_of_mem` and `rel_of_mem_W` give the basic instances.
  - `Rel.congr` and `Rel.congr_layer` change `V`.
  - `Rel.mul` (under `𝒰 ≤ W 0`) multiplies two relations.
  - `Rel.conj` conjugates by `b ∈ upper` when `b` normalizes `𝒰`, using
    `layerGroup_scale`.
  - `Rel.unique`: two layers of the same element agree modulo
    `layerGroup 𝒰 a`.
  - `Rel.approx_succ`: if the layer of `V` lies in `layerGroup 𝒰 a`, then
    `g` is in `𝒰 · W (a + 1)`.
  - `layerGroup_map` and `Rel.map` transport along ring maps that send `𝒰`
    into `𝒰'`.

## Provenance

The filtration of `U_N` by superdiagonals, with abelian quotients
`W a / W (a + 1)` given by the `(a + 1)`-st superdiagonal, is standard (see
Milne 2017, Chapter 16, for unipotent groups as subgroups of `U_N`). This
module is an internal formalization of that bookkeeping. It is used only to
run the layer-by-layer averaging argument of `Absolute/TriangularTorusLift`.
