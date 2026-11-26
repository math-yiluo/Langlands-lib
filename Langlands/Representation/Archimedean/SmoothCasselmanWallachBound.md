# Casselman–Wallach bound and the extension it implies

The declarations are in `Langlands.Archimedean`. The module states, but does not prove, the analytic estimate behind the Casselman–Wallach extension for real general linear groups. It proves that this estimate implies `RealSmoothCasselmanWallachExtensionStatement` of [SmoothCasselmanWallachStatement](SmoothCasselmanWallachStatement.md).

## The statement

Write `n = r + 1`, `D(R)` for `DerivativeSmoothVectors (matrixModel ℝ n) R`, and `∂_R(Xs)` for the continuous map `DerivativeSmoothVectors.derivativeCLM (matrixModel ℝ n) R Xs : D(R) → E`, the genuine word derivative `dR(X₁)(dR(X₂)(⋯ dR(Xₖ)y))` of a smooth vector `y` for the word `Xs = [X₁, …, Xₖ]` of real matrices. The empty word gives the underlying vector.

`RealSmoothCasselmanWallachBoundStatement.{uV, uE₁, uE₂}` has exactly the hypotheses of `RealSmoothCasselmanWallachExtensionStatement.{uV, uE₁, uE₂}`, with the same free carrier universes:

- a complex vector space `V : Type uV` with an action `ρ` of `Matrix.unitaryGroup (Fin n) ℝ` and a complex Lie algebra action `π` of `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ`, satisfying `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`;
- jointly continuous representations `R₁` and `R₂` of `Langlands.GeneralLinear n ℝ` by bounded operators on complex Banach spaces `E₁ : Type uE₁` and `E₂ : Type uE₂`;
- a linear equivalence `e : V ≃ₗ[ℂ] smoothKFinite ℝ n R₁` whose composite with the inclusion into `D(R₁)` satisfies `IsSmoothGKIntertwiner`, and a linear map `f : V →ₗ[ℂ] D(R₂)` satisfying `IsSmoothGKIntertwiner`.

The conclusion is a finite set `S` of words and a real constant `C` with

`‖∂_{R₂}([])(f v)‖ ≤ C · ∑_{Xs ∈ S} ‖∂_{R₁}(Xs)(e v)‖` for every `v : V`.

So the Banach norm of `E₂`, transported to `V` along `f`, is dominated by finitely many genuine word seminorms of `D(R₁)`, transported along `e`. Neither `f` nor the norm of `E₂` is otherwise restricted: `f` need not be injective or have dense image, and `R₂` need not be admissible.

## Source and derivation

This is a derived statement. The source is Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3, registered as `bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3` (SHA256 `f5f2e79d87532c9ac46389d7eb1606e0301eac0ba7c7972ab628e278e091ca3e`).

- On p.2 a norm on a Harish-Chandra module is *G-continuous* if its completion carries a Banach representation of `G`.
- On p.2, `p ≺ q` means `p(v) ≤ C q_k(v)` for some `k` and `C`, where `q_k` is a Sobolev norm of `q`. By §2.4.2 (p.10), `q_k(v)` is the square root of the sum of the squares `q(dπ(X₁^{m₁} ⋯ X_d^{m_d}) v)²` over the ordered basis monomials of degree at most `k`.
- Theorem 1.1 (p.3), the Casselman–Wallach theorem in this language, says that any two G-continuous norms on a Harish-Chandra module are Sobolev-equivalent. It is proved as Theorem 10.6 (p.45).
- Every representation on a Banach space has the growth required there. By §2.3, Example 2.7(a), p.8, any representation on a seminormed space is bounded for the maximal scale structure. By Lemma 2.1, p.6, the maximal and algebraic scale structures agree on the connected reductive group of matrices of positive determinant. The other component is its translate by a fixed orthogonal reflection `s`. Left multiplication by `s` preserves the algebraic scale `tr(g gᵀ) + tr(g⁻¹ g⁻ᵀ)`, and the operator of `s` is a single bounded operator. So the polynomial operator bound extends to all of `GL_n(ℝ)`. The Library's `BanachModerateGrowth` proves such a polynomial bound directly.

The orthogonal group `O(n)` is a maximal compact subgroup of the disconnected group `GL_n(ℝ)`, which lies in the class of groups treated in the source. The specialization to the present hypotheses runs as follows; `ε` denotes the empty-word map from a smooth carrier to its Banach space.

1. **The module.** Through `e`, the compact action and the derivatives on `V` are the genuine actions on compact-finite smooth vectors of `R₁`. So they satisfy the compatibility conditions of a `(𝔤, K)`-module, and each vector has a finite-dimensional compact orbit span. Let `S₀` be the orbit span of a nonzero vector. The `U(𝔤)`-span of `S₀` is stable under the compact action by compatibility, and under `𝔤`. Irreducibility makes it all of `V`, so `V` is finitely generated. With admissibility, `V` is a Harish-Chandra module in the sense of the source (Theorem 4.3, p.21, and p.22).
2. **The zero map.** If `f = 0` the bound holds with `S = ∅` and `C = 0`. From now on `f ≠ 0`. The kernel of `f` is stable under the compact action and under every `π(z ⊗ X) = z π(1 ⊗ X)`, because `f` intertwines both. So by irreducibility the kernel is zero and `f` is injective.
3. **The source norm.** `p(v) = ‖ε(e v)‖` is a norm on `V`, because `ε` and `e` are injective. Smooth vectors are norm dense in `E₁` (`dense_smoothVectors_units`), and compact-finite smooth vectors are dense in the smooth topology (`realSmoothCompactFiniteDensity`), which is finer than the norm topology along `ε`. So `ε(e(V))` is norm dense in `E₁`, and the completion of `(V, p)` is `E₁` with the action `R₁`, a Banach representation. Thus `p` is G-continuous. The derivatives `dπ` defining its Sobolev norms are the genuine derivatives of `e v`, by the derivative clause of `IsSmoothGKIntertwiner`.
4. **Polynomial annihilation.** Let `Ω = ∑ Xᵢ²` be the Cartan square sum for a basis `X₁, …, X_d` of the real matrices that is orthonormal for the positive Cartan inner product `⟨X, Y⟩ = tr(X Yᵀ)`. This is `−B(X, θY)` for the trace form `B(X, Y) = tr(X Y)` and the Cartan involution `θY = −Yᵀ`. It is invariant under conjugation by `O(n)`, so `π(Ω)` commutes with the compact action on `V`. In the Library this is the square sum over `RealCartan.realCartanBasis`, which `RealCartan.transportedCartanSquareSum_eq` identifies with the transported Cartan square sum of the closure lemma below. For `v` in `V`, its compact orbit span involves finitely many compact types. The sum of the corresponding isotypic components of `V` is finite-dimensional by admissibility and stable under `π(Ω)`. So `P(π(Ω)) v = 0` for a monic polynomial `P`. Applying `f`, which intertwines every `π(1 ⊗ X)` with the genuine derivative, gives `P(Ω)(f v) = 0` for the transported square sum of genuine derivatives on the smooth carrier of `R₂`.
5. **Closure invariance in `E₂`.** Let `C₂` be the norm closure of `ε(f(V))` in `E₂`. Let `λ` be a continuous linear functional on `E₂` vanishing on `C₂`, and let `w = f v`. The scalar coefficient `φ(g) = λ(R₂(g) ε w)` is smooth. Since `w` is a genuine smooth vector, every left-invariant derivative of `φ` along a word is `λ(R₂(g) ε(dR₂(word) w))`. So `φ` satisfies `P(Ω) φ = 0`, where `Ω` acts by the left-invariant vector fields `Xᵢᴸ`. The principal symbol of `Ω` at `g` is `ξ ↦ −∑ᵢ ξ(Xᵢᴸ(g))²`. The `Xᵢᴸ(g)` form a basis of the tangent space at `g`, so this symbol vanishes only at `ξ = 0`. The principal symbol of the monic polynomial `P(Ω)` of degree `m` is its `m`-th power. So `P(Ω)` is elliptic, with analytic coefficients in local analytic coordinates, and `φ` is real analytic: this is the calculation in the proof of Wallach, *Real Reductive Groups I*, Theorem 3.4.9 (registered as `wallach-1988-real-reductive-groups-i`, SHA256 `c021af2481d3ab479ab1cca0ae66e3e077fcfdec11b77df02b4b91cd31ba8dc9`, printed p.85, PDF p.105). That calculation uses only the differential equation for the scalar function, not a Hilbert structure. At the identity, each word derivative of `φ` is `λ(ε f(π(1 ⊗ X₁) ⋯ π(1 ⊗ Xₖ) v)) = 0`, since that vector lies in `ε(f(V))`. Analyticity makes `φ` vanish on the identity component. By Hahn–Banach, `R₂(g) ε w` lies in `C₂` for every `g` in the identity component, as in Wallach, Proposition 1.6.6 (printed pp.34–35, PDF pp.54–55). For an orthogonal element `k`, `R₂(k) ε(f v) = ε(f(ρ(k) v))` lies in `ε(f(V))`. The orthogonal group meets both components, so `C₂` is invariant under all of `GL_n(ℝ)`. The Library's `MixedOrbit.representation_mem_closure_of_stable` implements this closure step from the same polynomial-annihilation premise.
6. **The target norm.** `q(v) = ‖ε(f v)‖` is a norm by step 2. Its completion is `C₂` with the restriction of `R₂`, which is jointly continuous, so `q` is G-continuous. The vectors `ε(f v)` are smooth for this restricted action, since their orbits are smooth in `E₂` and stay in the closed subspace `C₂`. Their derivatives are the genuine derivatives in `E₂`. By the intertwining hypotheses on `f`, the compact action and the derivatives that `V` receives from `C₂` are `ρ` and `π`.
7. **Conclusion.** Theorem 1.1 gives `q ≺ p`: there are `k` and `C` with `q(v) ≤ C p_k(v)`. A square root of a sum of squares is at most the sum of the terms, and each ordered monomial is a word of real matrices. So `p_k(v) ≤ ∑_{Xs ∈ S} ‖∂_{R₁}(Xs)(e v)‖`, where `S` is the finite set of these monomial words of degree at most `k`. This is the asserted bound.

## The reduction

`realSmoothCasselmanWallachExtension_of_bound` proves

`RealSmoothCasselmanWallachBoundStatement.{uV, uE₁, uE₂} → RealSmoothCasselmanWallachExtensionStatement.{uV, uE₁, uE₂}`.

Helpers in `Langlands.Archimedean.SmoothCasselmanWallachBound`:

- `operatorWord R Xs` composes the genuine derived operators `DerivativeSmoothVectors.operator` along a word, and `gkWord π Xs` composes the algebraic operators `π(1 ⊗ X)`. `continuous_operatorWord` and `operatorWord_zero` record continuity and linearity at zero.
- `derivativeCLM_nil_operatorWord`: the underlying vector of `operatorWord R Xs y` is the word derivative `∂_R(Xs) y`. It is proved by induction from `derivativeCLM_nil_operator`, which uses `toSmooth_operator` and `smoothLieDerivative_apply`.
- `map_gkWord`: a linear map intertwining every `π(1 ⊗ X)` with the genuine derivative sends `gkWord π Xs v` to `operatorWord R Xs` of its image.

Proof of the reduction. Let `F = smoothKFinite ℝ n R₁` with the subspace topology, and let `t = f ∘ e⁻¹ : F → D(R₂)`. For a word `Xs` and `y = e v`, `map_gkWord` and `derivativeCLM_nil_operatorWord` give

`∂_{R₂}(Xs)(t y) = ∂_{R₂}([])(f (gkWord π Xs v))`.

The bound for the vector `gkWord π Xs v` and the same two lemmas for `e` bound its norm by `C · ∑_{Ys ∈ S} ‖∂_{R₁}(Ys)(operatorWord R₁ Xs y)‖`. This is a continuous function of `y` vanishing at zero, so every derivative coordinate of `t` is continuous, and `t` is continuous for the word-derivative topology. The compact-finite subspace is dense in `D(R₁)` (`realSmoothCompactFiniteDensity`), and `D(R₂)` is complete (`completeSpace_of_isContinuousRepresentation_units`). Mathlib's `ContinuousLinearMap.extend` along the inclusion of `F` gives a continuous linear `T : D(R₁) → D(R₂)` with `T (e v) = f v`. For each real direction `X`, both `T ∘ dR₁(X)` and `dR₂(X) ∘ T` are continuous and agree on `F` by the two intertwining hypotheses, so they agree everywhere by density. The same argument, with the continuous actions `SmoothAction.derivativeAction` of orthogonal elements, gives compact equivariance. Finally `smoothRealGroupIntertwining` upgrades compact and Lie equivariance of a continuous map to equivariance for every element of `GL_n(ℝ)`.

The reduction uses only the bound; irreducibility and admissibility are passed to it unchanged.
