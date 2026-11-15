# The bottom case of Stacks Lemma 11.4 (steps (19)–(26))

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.4
(Tag 07FJ), in `CharPResolutionAssembly`. It proves the "bottom" input of Lemma 9.2 used in
step (18): after killing `(γ₁ᵉ, …, γ_dᵉ)`, the problem factors through a smooth algebra.
All declarations are in the namespace `Langlands.CommutativeAlgebra.Popescu.CharP`.

## Difference from the source

The source reduces the bottom problem in several steps:
- (20) to `(R/I)_𝔯`;
- (22) to `(R/JR)_𝔭`;
- (23) to `(R/𝔭ⁿR)_𝔭`;
- (24) to `B` instead of `C`;
- (25)–(26) to a factorization through `D'[t₁, …, t_d]`.

In the Lean proof, the bottom hypothesis of `SequenceDimZeroResolutionStatement` (Lemmas
9.2 and 9.4 combined) is stated for arbitrary surjections `σ : R → R₁` and
`τ : Λ → Λ₁` killing `(γᵢᵉ)`, and a prime `Q` of `Λ₁` over `q`. So the Lean proof maps
everything directly into `L₁ = (R₁)_{Q ∩ R₁}` and `(Λ₁)_Q`:

- `κ : K_𝔭/𝔭ⁿ → L₁` and `ρ : Λ_q/qⁿΛ_q → (Λ₁)_Q` exist because the `tᵢ` and the `δᵢ`
  become units. Then `πᵢᵉ ↦ 0`, and `𝔭ⁿ ⊆ (πᵢᵉ)` (respectively `qⁿΛ_q ⊆ (πᵢᵉ)Λ_q`).
  This replaces steps (21)–(23).
- Instead of `D'[t₁, …, t_d]`, the smooth algebra is `T = L₁ ⊗_{P̄} T₀`. Here `T₀` is a
  smooth `P̄`-algebra through which `P̄ ⊗_{k[x]} B → D` factors (step (25)), and
  `P̄ = K_𝔭/𝔭ⁿ`. The map `B → T` sends `xᵢ ↦ κ(πᵢ) tᵢ` and `zᵢⱼ ↦ tᵢ^{2N} ⊗ zᵢⱼ`. This is
  the "final twist" (26): `zᵢⱼ ↦ λᵢⱼ tᵢ^{2N}/δᵢ^{2N}`.
- `D` is the ring of Lemma 11.2 itself, not an enlargement (see `CharPStep13.md`).
- Step (24) is not needed. The assembly works with `B` directly and composes with the
  retraction `C → B`.

## Declarations

- `minimal_of_pow_le q τ hτ p δ e n hδ hτ0 hqn Q hQ`. Assume:
  - `τ : Λ → Λ₁` is surjective and kills `(pᵢδᵢ)ᵉ`, with `δᵢ ∉ q`;
  - `qⁿΛ_q ⊆ (pᵢᵉ)Λ_q`;
  - `Q` is a prime of `Λ₁` with `τ⁻¹(Q) = q`.

  Then `Q` is a minimal prime of `Λ₁`. **Proof.** Let `Q' ⊆ Q` be prime. Then
  `pᵢᵉ ∈ τ⁻¹(Q')`, since `τ(δᵢ)ᵉ ∉ Q'`. The prime `τ⁻¹(Q')Λ_q` contains `qⁿΛ_q`, hence
  `qΛ_q`. Contracting gives `q ⊆ τ⁻¹(Q')`, so `Q' = Q`. This is the minimality of
  `qΛ_q/IΛ_q` in step (20): "Apply Lemma 9.4 to the situation in (18)".
- `exists_bottom_aux hES ιk N a πP abar habark w hrelD κ ℓ μ hℓκ tL` (generic core of
  (25)–(26)). The data are:
  - an essentially smooth `P`-algebra `D`;
  - `ā : A → D`, compatible with `ιk : k → P`;
  - `πᵢ ∈ P` and `wᵢⱼ ∈ D` with `πᵢ^{2N} = Σⱼ wᵢⱼ ā(aⱼ)` in `D`;
  - ring maps `κ : P → L`, `ℓ : L → M` and `μ : D → M` with `ℓ ∘ κ = μ ∘ (P → D)`;
  - elements `tᵢ ∈ L`.

  It gives:
  - a smooth `L`-algebra `T`;
  - `β : B → T` with `xᵢ ↦ κ(πᵢ) tᵢ`, compatible with `k`;
  - `v : T → M` extending `ℓ`, with `v ∘ β = μ ∘ ā` on `A` and
    `v(β(zᵢⱼ)) = ℓ(tᵢ)^{2N} μ(wᵢⱼ)`.

  **Proof.**
  1. Make `P` a `k[x]`-algebra via `xᵢ ↦ πᵢ` (a local instance).
  2. `liftHom` (module `CharPTools`) gives `B → D` with `xᵢ ↦ πᵢ` and `zᵢⱼ ↦ wᵢⱼ`.
     Hence `P ⊗_{k[x]} B → D` (`Algebra.TensorProduct.lift`).
  3. `hasSmoothFactorizations_of_essentiallySmooth` (module `CharPTools`) factors it
     through a smooth `P`-algebra `T₀`.
  4. Put `T = L ⊗_P T₀`. It is smooth over `L` by base change. `β` is again `liftHom`,
     and the relation `(κ(πᵢ)tᵢ)^{2N} = Σⱼ tᵢ^{2N} zᵢⱼ aⱼ` holds by `rel_eq`.
  5. `v = Algebra.TensorProduct.lift ℓ (μ ∘ (T₀ → D))`.

  Making `P` concrete here caused instance-search timeouts, so this core is stated for
  generic rings.
- `exists_bottom φ q 𝔭 h𝔭 hn ψ hψ hES hψφ f hf N a π δ hδ lam w hlam hw e h𝔭n hqn σK t τ
  hστ htτ hσ0 Q hQ`. This specializes the core to:
  - `P = K_𝔭/𝔭ⁿ` and `ψ : D → Λ_q/qⁿΛ_q` from Lemma 11.2;
  - `L = L₁` and `M = (Λ₁)_Q`.

  The data are:
  - `πᵢ ∈ K` and `δᵢ ∉ q`;
  - `λᵢⱼ` with `(δᵢφ(πᵢ))^{2N} = Σⱼ λᵢⱼ f(aⱼ)` and `λᵢⱼ ≡ δᵢ^{2N} ψ(wᵢⱼ)` modulo
    `qⁿΛ_q`;
  - `σK : K → R₁`, `tᵢ ∈ R₁` and `τ : Λ → Λ₁`, compatible (`hστ`, `htτ`), with
    `(σK(πᵢ) tᵢ)ᵉ = 0`.

  The conclusion gives `T` smooth over `L₁`, `β : B → T` and `v : T → (Λ₁)_Q`, with:
  - `xᵢ ↦ σK(πᵢ) tᵢ`;
  - `v` restricting to `L₁ → (Λ₁)_Q` (`Localization.localRingHom`);
  - `v ∘ β` sending `a ↦ τ(f(a))`, `xᵢ ↦ τ(φ(πᵢ)δᵢ)` and `zᵢⱼ ↦ τ(λᵢⱼ)`.

  **Proof.**
  1. `κ` and `ρ` are `Ideal.Quotient.lift` of `IsLocalization.lift`, as explained above.
  2. `ā : A → D`: `ψ` is injective (`injective_of_flat_of_isLocalHom`) and its range
     contains the image of `A` (`hf`), so `ā = ψ⁻¹ ∘ f̄` (`RingEquiv.ofBijective`).
  3. The relation `πᵢ^{2N} = Σⱼ wᵢⱼ ā(aⱼ)` in `D` follows from `hlam` and `hw` after
     cancelling the unit `δᵢ^{2N}` in `Λ_q/qⁿΛ_q` and using injectivity of `ψ`.
  4. Apply `exists_bottom_aux` with `μ = ρ ∘ ψ`. The value on `zᵢⱼ` is
     `τ(δᵢ)^{2N} ρ(ψ(wᵢⱼ)) = ρ(λ̄ᵢⱼ) = τ(λᵢⱼ)`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.4 (Tag 07FJ, printed pp. 28-31,
steps (17)–(26) and their justifications), Lemma 9.4 (Tag 07FA).
