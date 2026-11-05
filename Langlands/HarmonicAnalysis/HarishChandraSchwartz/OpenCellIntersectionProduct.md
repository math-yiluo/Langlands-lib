# Products of a contracted subgroup through an open cell

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntersectionProduct`,
namespace `Langlands.HarishChandraSchwartz`.

## Purpose and provenance

Provenance: internal. In Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1, printed p. 279 (PDF p. 45), the standard intertwining
integral over `(U ∩ U') \ U'` is computed through the product decomposition
`U' = (U ∩ U') (Ū ∩ U')`, where `Ū` is the radical opposite to `U`. The source uses this
decomposition without proof; for reductive groups it is the usual product of root subgroups.
This module proves an abstract topological-group form of the decomposition, together with the
statement that multiplication is a homeomorphism. The proof uses only an open cell and two
contracting conjugations. It is designed to be applied later to the rational points of the
dynamic subgroups of a smooth affine group, where `P × Ū → G`, `(p, v) ↦ p v⁻¹`, is the open
cell (public `isOpenEmbedding_openCellMap_rationalPoint`, module `OpenCellPoints`), `a` is the
value at a uniformizer of the cocharacter of `P'` and `b` the value at a uniformizer of the
cocharacter of `P`. That application is not made here. The argument is not transcribed from
a source.

## Setting

`Γ` is a group with a topology making it a topological group. `P`, `V`, `U`, `U'`, `M` are
subgroups of `Γ` and `a, b ∈ Γ`. `openCellMap : P × V → Γ` is the public map
`(p, v) ↦ p v⁻¹` (module `OpenCellIntegration`). `U.subgroupOf U'` is the subgroup of `U'`
consisting of the elements lying in `U`, with the subspace topology.

## Declarations

- `IsOpenCellContraction P V U U' M a b` (definition, a structure of propositions). Its fields:
  - `isOpenEmbedding`: `openCellMap : P × V → Γ` is an open embedding;
  - `unipotent_le`: `U ≤ P`;
  - `mem_normalizer_parabolic`, `mem_normalizer_opposite`: `a` normalizes `P` and `V`;
  - `tendsto_conj`: for every `x ∈ U'`, `a ^ n * x * (a ^ n)⁻¹ → 1` as `n → ∞`;
  - `mem_of_tendsto_conj`: conversely, every `x ∈ Γ` with `a ^ n * x * (a ^ n)⁻¹ → 1` lies in
    `U'`;
  - `exists_levi_mul`: every `p ∈ P` is `m * u` with `m ∈ M` and `u ∈ U`;
  - `tendsto_levi_conj`: for every `u ∈ U`, `b ^ n * u * (b ^ n)⁻¹ → 1`;
  - `commute_levi`: `b` commutes with every element of `M`;
  - `isClosed`: `U'` is closed in `Γ`;
  - `mem_normalizer_target`: `b` normalizes `U'`;
  - `eq_one_of_mem_levi`: the only element of `M` lying in `U'` is `1`.
- `subgroupProductMap U V U'` (definition): the map
  `(U.subgroupOf U') × (V.subgroupOf U') → U'`, `(h, k) ↦ h * k`.
  `coe_subgroupProductMap` (simp) gives its value in `Γ`.
- `conj_mem_of_mem_normalizer`, `inv_conj_mem_of_mem_normalizer`: if `g` normalizes `H` and
  `x ∈ H`, then `g x g⁻¹ ∈ H` and `g⁻¹ x g ∈ H`.

For `hc : IsOpenCellContraction P V U U' M a b`:

- `hc.exists_mul_eq`: every `x ∈ U'` is `h * k` with `h ∈ U ∩ U'` and `k ∈ V ∩ U'`.
- `hc.eq_of_mul_eq`: if `h, h' ∈ U`, `k, k' ∈ V` and `h * k = h' * k'`, then `h = h'` and
  `k = k'`.
- `hc.isHomeomorph_subgroupProductMap`: `subgroupProductMap U V U'` is a homeomorphism.
- `hc.productHomeomorph : (U.subgroupOf U') × (V.subgroupOf U') ≃ₜ U'` (definition), the
  bundled homeomorphism, with `productHomeomorph_apply`: its value at `(h, k)` is `h * k`
  in `U'`.

## Proofs as implemented

**Existence.** Let `x ∈ U'`. The range `Ω` of `openCellMap` is open and contains
`openCellMap (1, 1) = 1`. Since `a ^ n x a⁻ⁿ → 1`, some `a ^ N x a⁻ᴺ` lies in `Ω`, say
`a ^ N x a⁻ᴺ = q₁ q₂⁻¹` with `q₁ ∈ P`, `q₂ ∈ V`. Put `p₀ = a⁻ᴺ q₁ a ^ N ∈ P` and
`v₀ = a⁻ᴺ q₂ a ^ N ∈ V` (normalization by `a`); then `x = p₀ v₀⁻¹`.

For every `n`, `a ^ n x a⁻ⁿ = openCellMap (a ^ n p₀ a⁻ⁿ, a ^ n v₀ a⁻ⁿ)`. Because `openCellMap`
is inducing, convergence of the left side to `1 = openCellMap (1, 1)` gives convergence of the
pairs to `(1, 1)` in `P × V` (`IsInducing.tendsto_nhds_iff`). In particular
`a ^ n v₀ a⁻ⁿ → 1`, so `v₀ ∈ U'` by `mem_of_tendsto_conj`, and `p₀ = x v₀ ∈ U'`.

Write `p₀ = m u` with `m ∈ M`, `u ∈ U`. As `b` commutes with `m`,
`b ^ n p₀ b⁻ⁿ = m (b ^ n u b⁻ⁿ) → m`. Each `b ^ n p₀ b⁻ⁿ` lies in `U'` (normalization by `b`),
and `U'` is closed, so `m ∈ U'`. Hence `m = 1` and `p₀ = u ∈ U`. Take `h = p₀`, `k = v₀⁻¹`.

**Uniqueness.** `h k = h' k'` says `openCellMap (h, k⁻¹) = openCellMap (h', k'⁻¹)`, using
`U ≤ P`. Injectivity of `openCellMap` gives `h = h'` and `k⁻¹ = k'⁻¹`.

**Homeomorphism.** By Mathlib's `isHomeomorph_iff_isEmbedding_surjective` it suffices to prove
that `subgroupProductMap` is inducing, injective and surjective. Injectivity is uniqueness and
surjectivity is existence. For inducing, the composite with the inclusion `U' → Γ` equals
`openCellMap ∘ (ψ₁ × ψ₂)`, where `ψ₁ (h) = h ∈ P` and `ψ₂ (k) = k⁻¹ ∈ V`. The maps `ψ₁`, `ψ₂`
are inducing because their composites with the subtype inclusions into `Γ` are composites of
subtype inclusions and, for `ψ₂`, of inversion, a homeomorphism of `Γ`
(`IsInducing.of_comp_iff`). Products of inducing maps are inducing (`IsInducing.prodMap`), and
`openCellMap` is inducing. Since the inclusion `U' → Γ` is inducing, `IsInducing.of_comp_iff`
shows that `subgroupProductMap` is inducing.

## Scope

Every hypothesis is a field of `IsOpenCellContraction`; none is proved here for an actual
group. In particular this module does not show that the rational points of a dynamic radical
`U'` are characterized by contraction, that the open cell exists for a given group, or that the
Levi meets `U'` trivially. It proves nothing about Haar measures on the factors or on the
quotient `(U ∩ U') \ U'`, and nothing about convergence of intertwining integrals.
