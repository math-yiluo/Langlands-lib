# Coefficients, smooth endomorphisms and the formal degree: statements

Author: Worker 6. Module `Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.4, printed pp.90–92 / PDF pp.96–98: the construction after the Theorem, (IV.1.4.1)–(IV.1.4.3), the Proposition, the definition of the formal degree and its Remarks. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## The source

In IV.1.4, `G` is a t.d. group, unimodular and countable at infinity, with a fixed Haar measure, and `(τ, W)` is an irreducible compact representation. Renard identifies `𝒟(G)` with `H(G)` through the Haar measure and considers the `G × G`-equivariant algebra map `τ : 𝒟(G) → End(W)₀`, `f ↦ τ(f)`, into the smooth part of `End(W)` for the action `((g₁, g₂) · λ)(v) = g₁ · λ(g₂⁻¹ · v)`. The steps are:

- **(IV.1.4.1).** The map `α : W ⊗ W̃ → End(W)₀`, `α(w ⊗ λ)(v) = λ(v) w` (IV.1.4.2), is an isomorphism of `G × G`-representations. Injectivity and equivariance are "clear", and surjectivity follows from a dimension count on `K × K`-invariants (IV.1.4.3). Renard remarks that the proof establishes (IV.1.4.1) for every admissible `W`.
- **The section.** With `φ : W ⊗ W̃ → 𝒟(G)`, `v ⊗ λ ↦ ˇφ_{v,λ}`, where `ˇφ_{v,λ}(g) = φ_{v,λ}(g⁻¹) = λ(τ(g⁻¹) v)` (IV.1.3), let `ψ : End(W)₀ → 𝒟(G)` be the linear map with `ψ ∘ α = φ`. Schur's lemma gives a scalar `κ(τ)` with `τ ∘ ψ = κ(τ) Id`.
- **Proposition.** (i) If `(ρ, E)` is an irreducible smooth representation not equivalent to `(τ, W)`, then `ρ(f) = 0` for every `f` in the image of `ψ`. (ii) `κ(τ) ≠ 0`.
- **Definition.** `d(τ) = κ(τ)⁻¹` is the formal degree of `τ`.
- **Remarks.** 1. `d(τ)` depends on the choice of Haar measure. 2. If `G` is compact and the Haar measure is normalized by `∫_G dμ_G = 1`, then the formal degree of an irreducible smooth representation of `G` is its dimension. 3. The formal degree of square-integrable irreducible representations is defined in IV.3.3.

## The Lean statements

The Hecke algebra is the published `Hecke.HeckeAlgebra μ`, the compactly supported locally constant functions with convolution for `μ`. Its action is the published `Hecke.heckeAction μ ρ hρ f v = ∫ f(g) ρ(g) v dμ(g)`, Renard's `ρ(f)`. The smooth dual `W̃` is the published `SmoothDual τ.representation`, and `HasCompactSmoothDualCoefficients` (module `CompactCoefficient/Classes`) says that every matrix coefficient `g ↦ λ(τ(g) v)` with `λ` smooth has compact support. By IV.1.3, Theorem, this is Renard's notion of a compact representation.

### `SmoothEndomorphismTensorStatement` (IV.1.4.1)

The hypotheses are a Hausdorff, locally compact, totally disconnected topological group `G` and an admissible `τ : SmoothRep.{0, u, v} ℂ G`. Let `α : τ ⊗[ℂ] SmoothDual τ →ₗ[ℂ] Module.End ℂ τ` be the lift of the bilinear map `(w, λ) ↦ λ(·) • w`, built from Mathlib's `LinearMap.smulRightₗ`, so that `α(w ⊗ λ)(v) = λ(v) w`. The conclusion is:

1. `α` is injective;
2. the range of `α` is the set of endomorphisms `A` for which some open subgroup `K` satisfies `τ(k₁) ∘ A ∘ τ(k₂) = A` for all `k₁, k₂ ∈ K`.

The set in 2 is `End(W)₀`. An endomorphism is a smooth vector for the `G × G`-action exactly when it is fixed by `K × K` for some open subgroup `K`, since such products form a neighbourhood basis of the identity in `G × G`. Being fixed by `K × K` means `τ(k₁) A τ(k₂⁻¹) = A`, which is the displayed condition. The `G × G`-equivariance of `α` is a direct computation and is not restated. Admissibility is needed for surjectivity: if `W^K` is infinite-dimensional, an endomorphism that is the identity on `W^K` and zero on `W(K)` is smooth but has infinite rank.

### `CompactCoefficientFormalDegreeStatement` (Proposition and definition of `d(τ)`)

The hypotheses are those of the companion IV.1.5 statement `CompactProjectionDistributionStatement`. `G` is a Hausdorff, locally compact, totally disconnected, σ-compact group. `μ` is a regular Haar measure on `G` that is also right invariant, which encodes unimodularity together with the bi-invariant Haar measure. `τ` is irreducible with `HasCompactSmoothDualCoefficients τ.representation`.

Write `IsCoefficient w λ f` for `∀ g, f g = λ(τ(g⁻¹) w)`, i.e. `f = ˇφ_{w,λ}` as functions. The conclusion is the conjunction of:

1. for all `w` and smooth `λ`, some `f : Hecke.HeckeAlgebra μ` satisfies `IsCoefficient w λ f`: `ˇφ_{w,λ}` is a test function. Renard uses this when defining `φ`;
2. (i) for every irreducible `ρ : SmoothRep.{0, u, v} ℂ G` with `IsEmpty (ρ ≅ τ)` and every `f` with `IsCoefficient w λ f`, `heckeAction μ ρ f = 0`;
3. (ii) there is `κ : ℂ` with `κ ≠ 0` such that `heckeAction μ τ f x = (κ · λ(x)) • w` for all `w`, `λ`, `f` with `IsCoefficient w λ f`, and all `x`.

Part 3 is `τ(ˇφ_{w,λ}) = κ(τ) α(w ⊗ λ)`, which is `τ ∘ ψ = κ(τ) Id` evaluated on `α(w ⊗ λ)`, since `ψ(α(w ⊗ λ)) = ˇφ_{w,λ}`. By (IV.1.4.1) these elements span `End(W)₀`, so part 3 determines `τ ∘ ψ`. The scalar `κ` is unique: choose `w ≠ 0` and a smooth `λ` with `λ(w) = 1`. Such a `λ` exists because smooth functionals separate points, by the decomposition `W = W^K ⊕ W(K)` of III.1.5. Its inverse is the formal degree `d(τ)`. Part 2 is Renard's (i), since the image of `ψ` is spanned by the `ˇφ_{w,λ}` and `ρ(f)` is linear in `f`. Together with (IV.1.4.1), part 3 also gives the surjectivity of `τ : 𝒟(G) → End(W)₀` announced in the source, with section `κ(τ)⁻¹ ψ`.

The representations `ρ` range over the same carrier universe `v` as `τ`, as in the companion IV.1.5 statement.

### `CompactGroupFormalDegreeStatement` (Remark 2)

The hypotheses are a compact Hausdorff totally disconnected group `G`, a Haar measure `μ` with `μ univ = 1`, and an irreducible smooth `τ`. The conclusion is:

1. `FiniteDimensional ℂ τ`;
2. for all `w`, smooth `λ` and `f` with `f(g) = λ(τ(g⁻¹) w)`, and all `x`, `heckeAction μ τ f x = ((finrank τ)⁻¹ · λ(x)) • w`.

Part 2 says that the scalar `κ(τ)` of the previous statement is `(dim τ)⁻¹`, so `d(τ) = dim τ`. A compact group is σ-compact and unimodular. Every smooth representation of it has compactly supported coefficients, and the coefficients `ˇφ_{w,λ}` are test functions. The previous statement therefore applies, and Remark 2 identifies its constant. Part 1 makes `finrank` the actual dimension. Without it, Mathlib's `Module.finrank` of an infinite-dimensional space is `0`.

`CompactFormalDegreeStatements` is the conjunction of the three statements.

## Remarks

- Remark 1, the dependence of `d(τ)` on the Haar measure, is not stated separately. Replacing `μ` by `c μ` multiplies every `τ(f)` by `c`, so it multiplies `κ(τ)` by `c` and divides `d(τ)` by `c`. For square-integrable representations, the published `representationFormalDegree_smul_measure` (module `Plancherel/FormalDegreeHaarScaling`) records the corresponding scaling of the Schur formal degree.
- Remark 3 refers to IV.3.3. Applying a smooth functional `λ'` to part 3 gives `∫ λ(τ(g⁻¹) w) λ'(τ(g) x) dμ(g) = κ(τ) λ(x) λ'(w)`, which is a Schur orthogonality relation on `G` with formal degree `κ(τ)⁻¹`. The IV.3.3 relations are stated on `G / Z(G)` in Worker 6's `SchurOrthogonalityStatement` (module `UnitarySquareIntegrableStatements`), and a Schur degree for a central subgroup is published as `HarishChandraSchwartz.formalDegree`. Comparing these degrees with `κ(τ)⁻¹` requires matching the Haar measures on `G` and on the quotient. That comparison is not formalized here.
- The Theorem of IV.1.4 (`V = V(τ) ⊕ V(τ)^⊥`) is the published `CompactCoefficientProjectorStatement` (Bernstein–Zelevinsky 2.42–2.44). The idempotents `e_{K,τ} = d(τ) ψ(τ(e_K))` of IV.1.5 are stated in `CompactProjectionDistributionStatement`.
- The proofs (the dimension count (IV.1.4.3), Schur's lemma for the irreducible `G × G`-representation `W ⊗ W̃` of III.1.14, and the completeness lemma III.1.11) are not formalized here.
