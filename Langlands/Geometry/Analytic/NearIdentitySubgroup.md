# Transitivity of the test relations and the subgroups `G_τ(X)`

Author: Worker 57.

Berkovich makes the automorphism group `G(X)` of an analytic space a
topological group. The open subgroups `G_ε(X)` of automorphisms near the
identity define its topology. The Library defines the sets
`nearIdentity τ` of a test triple `τ` (`ContinuousAnalyticAction`). This
module shows that each of them is a subgroup of `Aut X`. On the way it proves
that the test relation `IsNear τ` is transitive.

## Original source

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`, §6,
printed p.557 / PDF p.19: "We endow the group G(X) with the topology induced
from Mor(X, X). It is easy to see that G(X) is really a topological group
(not necessarily Hausdorff), and its topology is defined by the system of the
subgroups G_ε(X) = {σ ∈ G(X) | σ(U_i) = U_i, ρ(σ_i^* f_ij − f_ij) ≤ t_ij}
for ε ∈ 𝔈(X) as above."

The Library's `nearIdentity τ` is Berkovich's set `G_ε(X)` for the element
`ε` of `𝔈(X)` given by the single test triple `τ`. The full quotation and
this correspondence are in the Library's
`Langlands/Geometry/Analytic/ContinuousAnalyticAction.md`. Berkovich calls
these sets subgroups without proof ("it is easy to see"). The proofs below
are derived; they use the strong triangle inequality of the points of the
spectrum.

## Declarations

All declarations are in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. `K` is a complete ultrametric
normed field.

- `StrongNear.of_common`: let `x₀ x₁ x₂ : T ⟶ B` be strong maps and `τ` a test
  triple of `B`. If `StrongNear τ x₀ x₁` and `StrongNear τ x₀ x₂`, then
  `StrongNear τ x₁ x₂`.
- `IsNear.trans`: `IsNear τ φ ψ` and `IsNear τ ψ χ` imply `IsNear τ φ χ`, for
  morphisms `φ ψ χ : Y ⟶ X` of `LocalizedCategory` and a test triple `τ` of
  `X`.
- `IsNear.comp_of_isNear_id`: let `φ ψ : Y ⟶ Y` with `IsNear τ φ (𝟙 Y)` and
  `IsNear τ ψ (𝟙 Y)`. Then `IsNear τ (φ ≫ ψ) (𝟙 Y)`.
- `nearIdentitySubgroup τ : Subgroup (Aut X)`: the subgroup with carrier
  `nearIdentity τ`.
- `mem_nearIdentitySubgroup`: `σ ∈ nearIdentitySubgroup τ ↔ σ ∈ nearIdentity τ`
  (by definition).

## Proofs

**`StrongNear.of_common`.** The three conditions of `StrongNear` are checked
in turn.

1. *Preimages.* `x₁⁻¹(U) = x₀⁻¹(U) = x₂⁻¹(U)`.
2. *Covering.* A point `y` of `x₁⁻¹(U)` lies in `x₀⁻¹(U)`. Hence it lies in a
   chart `i₁` that `x₀` and `x₁` both send into `U`, and in a chart `i₂` that
   `x₀` and `x₂` both send into `U`. The charts form a net, so
   `exists_chart_mem_subset_inter` gives a chart `l ∋ y` inside `i₁ ∩ i₂`.
   Then `x₁` and `x₂` both send `l` into `U`.
3. *Bound.* Let `i` be a chart that `x₁` and `x₂` send into `U`. Then `x₀`
   also sends `i` into `U`, because `x₀⁻¹(U) = x₁⁻¹(U)`. Write `a_k` for
   `x_k^*f` on the chart `i`. For every point `p` of the spectrum of the chart
   algebra,
   `p(a₁ − a₂) = p(−(a₀ − a₁) + (a₀ − a₂)) ≤ max(p(a₀ − a₁), p(a₀ − a₂)) ≤ t`.
   This uses that `p` is nonarchimedean (`BanachSpectrum.isNonarchimedean`)
   and that `p(−x) = p(x)`.

**`IsNear.trans`.** The relations `IsNear τ ψ φ` (symmetry) and `IsNear τ ψ χ`
are merged by the Library's `exists_strongNear_numerators`. This gives one
quasi-isomorphic refinement `s : S ⟶ presentationOf Y` and strong numerators
`x₀ x₁ x₂` of `ψ`, `φ`, `χ` with `StrongNear τ x₀ x₁` and
`StrongNear τ x₀ x₂`. Then `StrongNear.of_common` gives `StrongNear τ x₁ x₂`,
and `isNear_iff_numerators` gives `IsNear τ φ χ`.

**`IsNear.comp_of_isNear_id`.** Precomposing `IsNear τ ψ (𝟙 Y)` with `φ`
(`IsNear.precomp`) gives `IsNear τ (φ ≫ ψ) φ`. Transitivity with
`IsNear τ φ (𝟙 Y)` finishes the proof.

**`nearIdentitySubgroup`.** In `Aut X`, `(σ * σ').hom = σ'.hom ≫ σ.hom`.

- *Identity:* the identity is in the set by the Library's
  `one_mem_nearIdentity`.
- *Products:* closure under products is `IsNear.comp_of_isNear_id`.
- *Inverses:* for `σ ∈ nearIdentity τ`, precompose `IsNear τ σ.hom (𝟙 X)`
  with `σ.inv`. This gives `IsNear τ (𝟙 X) σ.inv`, and symmetry gives
  `σ⁻¹ ∈ nearIdentity τ`.
