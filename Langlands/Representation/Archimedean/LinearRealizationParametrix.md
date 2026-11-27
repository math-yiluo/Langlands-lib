# A local Sobolev identity on Lie groups with a closed linear realization

`Langlands.Representation.Archimedean.LinearRealizationParametrix`, namespace
`Langlands.Archimedean`.

## Statement

`exists_sum_integral_iteratedLieDerivative`. Let `G` be a Lie group modelled on a real normed space
`E` (`LieGroup 𝓘(ℝ, E) ∞ G`) that is a topological group with Borel measurable structure, let
`ρ : G →* 𝔸ˣ` be a closed linear realization (`LinearLieGroup.IsClosedLinearRealization`) in the
units of a finite-dimensional real Banach algebra `𝔸`, and let `μ` be a left Haar measure on `G`.
There are `N`, words `word : Fin N → List E` and continuous compactly supported `κ_j : G → ℂ` such
that for every complex Banach space `V` (in a fixed universe), every `π : G →* (V →L[ℂ] V)` with
`g ↦ π(g) v` continuous for each `v`, and every smooth vector `w` of `π`,

`w = ∑ⱼ ∫ κ_j(g) • π(g)(iteratedLieDerivative 𝓘(ℝ, E) π (word j) w) dμ(g)`.

The words and the functions do not depend on `V`, `π` or `w`.

## Proof

Let `H = ρ(G)`, a closed subgroup of `𝔸ˣ` with `IsExpLieAlgebra H 𝔥` for its Lie algebra
`𝔥 = lieSubmodule H _` (`IsClosedLinearRealization.isExpLieAlgebra`), and let
`e = rangeEquiv : G ≃ₜ* H`. The image `μ.map e` is a left Haar measure on `H`
(`ContinuousMulEquiv.isHaarMeasure_map`, with the Borel structure on `H`). Choose a basis `b` of `𝔥`
indexed by `Fin n`.

1. `exists_continuous_density_prodExp_smul` for `μ.map e` and `b` gives `ε > 0`.
2. The curves `γᵢ(s) = e⁻¹(exp(s bᵢ))` are smooth maps `ℝ → G` (`contMDiff_expG_comp` and the
   smoothness of `e⁻¹`, `contMDiff_rangeRestrict_and_symm`) and homomorphisms
   (`expG_add_smul`). `OneParameterParametrix.exists_sum_integral_curveProd` for `γ` and `ε` gives
   words `word j` and continuous kernels `K_j` on `ℝⁿ` supported in the closed `ε`-ball with
   `w = ∑ⱼ ∫ K_j(t) π(curveProd γ t)(dπ(word j) w) dt`.
3. `curveProd γ t = e⁻¹(prodExp b t)`, since `e⁻¹` is a homomorphism. For each `j`, step 1 gives a
   continuous compactly supported `κ'_j` on `H` with
   `∫ κ'_j(y) • f(y) d(μ.map e)(y) = ∫ K_j(t) • f(prodExp b t) dt` for continuous `f`; apply it to
   `f(y) = π(e⁻¹ y)(dπ(word j) w)` and change variables along the homeomorphism `e`
   (`integral_map_equiv`). So `κ_j = κ'_j ∘ e` works.

The words are built from the tangent vectors `mfderiv γᵢ 0 1 ∈ E`; they are not computed further,
since only their existence is asserted.

## Literature

The method is that of J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs
indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, proof of Theorem 3.1,
steps (1)–(3), pp. 6–7 of the English translation *Factorizations of infinitely differentiable
functions and smooth vectors* (paginated 1–24), with the second-order one-variable identity of
`OneParameterParametrix` in place of their Lemma 2.5; see that module's page. An identity of this
form bounds `‖w‖` by finitely many of the quantities `‖π(g) dπ(word j) w‖` with `g` in a compact
set; compare the local Sobolev estimate of J. Bernstein, *On the support of Plancherel measure*,
J. Geom. Phys. 5 (1988), §3.4, Key Lemma, p. 686, whose proof (p. 687, steps 1–2) reduces to an a
priori estimate in local coordinates.
