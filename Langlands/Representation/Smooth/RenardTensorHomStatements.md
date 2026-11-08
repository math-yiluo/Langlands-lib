# Regular representations, tensor products and smooth Hom: statements

Author: Worker 6. Module `Langlands.Representation.Smooth.RenardTensorHomStatements`, namespace `Langlands.Renard.Smooth`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026: III.1.2, Proposition (printed pp.58–59 / PDF pp.64–65); III.1.3, Example (printed p.59 / PDF p.65); III.1.15, Proposition, Lemma, Corollary and Theorem (printed pp.67–70 / PDF pp.73–76). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## Conventions

`G` is a group with a topology making it a Hausdorff, locally compact, totally disconnected topological group, Renard's t.d. groups. Representations are Mathlib's `Representation ℂ G V` with the published `IsSmooth`. Mathlib's `Representation.tprod π₁ π₂` is the diagonal action on `V₁ ⊗ V₂`, and `Representation.linHom π₁ π₂` the action `(g φ)(v) = π₂(g) φ(π₁(g⁻¹) v)` on `Hom_ℂ(V₁, V₂)`, Renard's `π_ρ`. `smoothVectors` and `smoothPart` are the published smooth vectors and smooth part (module `Smooth/SmoothPart/Definitions`), Renard's `Hom(W, V)₀`.

## The Lean statements

### `RegularRepresentationSmoothStatement` (III.1.2, Proposition)

Call `f : G → ℂ` uniformly locally constant if `f(k x k') = f(x)` for all `k, k'` in some compact open subgroup `K`, i.e. `f ∈ 𝒞^∞(G, K)`; these are Renard's `𝒞^∞_unif(G)`. The conclusion is the conjunction of:

1. for every `g`, the left translate `x ↦ f(g⁻¹ x)` and the right translate `x ↦ f(x g)` of a uniformly locally constant `f` are uniformly locally constant;
2. every uniformly locally constant `f` is fixed under both translations by some open subgroup;
3. the published left and right regular representations `GroupAction.leftTests` and `GroupAction.rightTests` on test functions `𝒟(G)` (module `HarmonicAnalysis/GroupAction`) are smooth.

Parts 1 and 2 say that `l` and `r` preserve `𝒞^∞_unif(G)` and act smoothly on it. The published representations already preserve `𝒟(G)`.

### `LeftRegularHeckeActionStatement` (III.1.3, Example)

For a left Haar measure `μ` and any smoothness proof `hl` of `leftTests`, the published integrated action satisfies `heckeAction μ leftTests hl T f = T * f`, the convolution in `HeckeAlgebra μ`. This is Renard's `l(T) · f = T ∗ f` for `T ∈ H(G)` and `f ∈ 𝒟(G)`, through the identification of `𝒟(G)` with `H(G)` by `μ`. The hypothesis `hl` is the proposition of part 3 above. Since it is a proposition, the action does not depend on the choice of proof.

### `TensorHomAdjunctionStatement` (III.1.15, Lemma, Proposition and Corollary)

For representations `π₁, π₂, π₃` on carriers in a common universe `v`:

1. **Lemma.** If `π₁` is smooth, every smooth vector `φ` of `linHom π₁ π₂` takes values in `smoothVectors π₂`. This is Renard's `Hom((V₁)₀, V₂)₀ = Hom((V₁)₀, (V₂)₀)₀`.
2. **Proposition.** If all three are smooth, there is an equivalence of representations from the smooth part of `linHom (tprod π₁ π₂) π₃` to the smooth part of `linHom π₁ (smoothPart (linHom π₂ π₃))`, given by `e(φ)(x₁)(x₂) = φ(x₁ ⊗ x₂)`. This is Renard's natural isomorphism `Hom(V₁ ⊗ V₂, V₃)₀ ≃ Hom(V₁, Hom(V₂, V₃)₀)₀`, which he obtains from currying and the Lemma. Its naturality in the three variables is not restated.
3. **Corollary.** There is a linear equivalence `Hom_G(V₁ ⊗ V₂, V₃) ≃ Hom_G(V₁, Hom(V₂, V₃)₀)` of intertwiner spaces, given by the same formula.

Remark 1 of III.1.15 (the adjunction `• ⊗ V₂ ⊣ Hom(V₂, •)₀`) is the Corollary read as an adjunction, and Remark 2 (preservation of colimits and limits) is a formal consequence. Remark 3, on twisting by a character, is not restated.

### `TensorHomExactnessStatement` (III.1.15, Theorem)

For a smooth `π` on `V`, with objects of `M(G)` taken on carriers in `Type v`: a smooth representation is **projective** when every intertwiner from it to `Z` lifts through every surjective intertwiner `Y → Z` of smooth representations, and **injective** when every intertwiner from `X` to it extends along every injective intertwiner `X → Y` of smooth representations. These lifting properties are projectivity and injectivity in the abelian category of smooth representations. The conclusion is the conjunction of:

1. **(i)** if `ρ` is smooth and projective, so is `tprod ρ π`. Exactness of `• ⊗ V` is exactness of the tensor product over `ℂ` and is not restated;
2. **(ii), exactness.** For an injective intertwiner `i : W₁ → W₂` of smooth representations, every smooth vector `f` of `linHom σ₁ π` is `f' ∘ i` for some smooth vector `f'` of `linHom σ₂ π`. This is the surjectivity of `Hom(W₂, V)₀ → Hom(W₁, V)₀`, the nontrivial half of exactness;
3. **(ii), projectives.** If `ρ` is smooth and projective, `smoothPart (linHom ρ π)` is injective;
4. **(iii), exactness.** For a surjective intertwiner `q : W₂ → W₃` of smooth representations, every smooth vector `f` of `linHom π σ₃` is `q ∘ f'` for some smooth vector `f'` of `linHom π σ₂`. This is the surjectivity of `Hom(V, W₂)₀ → Hom(V, W₃)₀`;
5. **(iii), injectives.** If `ρ` is smooth and injective, `smoothPart (linHom π ρ)` is injective.

`RenardTensorHomStatements` is the conjunction of the four statements.

## Remarks

- The identification `(V₁ ⊗ V₂)_G ≅ V₁ ⊗_{H(G)} V₂` and the associativity (III.1.15.1) are not stated here.
- The proofs are not formalized here. Renard proves (iii) from the semisimplicity of `M(K)` for compact open `K`, which is Worker 6's published IV.1.1 statement `CompactGroupSmoothRepresentationStatement` (iii) (module `Compact/CompactGroupSmoothStatements`), and the remaining assertions from the Corollary.
