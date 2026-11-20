# Construction of the refined element

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). It holds the abstract
construction of the element `γ` with `T.b = γ`, combining the book's (2.2.8) with the
conjugation step (2.2.1). This is derived content, not a separately cited statement.

## `block_eq_of_commute`

Let `w` be an `L`-basis of `V` and let `z` commute with the action of `L`. Then each block
`ε_{jj} z ε_{ll}` equals `a · ε_{jl}`, where `a` is the `j`-th coordinate of `z(w_l)`.

## `exists_refined_element`

The setting is a local field `F` and a field `L` acting on `V` whose units normalize the chain
`𝓛`. The theorem assumes:

- `β` and `c` are actions of elements of `L`;
- every endomorphism commuting with `β` and `c` commutes with all of `L`;
- an additive `s` with the properties used by `refinement_core`, together with the inputs U1
  and V1 (see `RefinementCore.md`);
- U2: if `z ∈ 𝔓^{-r}` and `s(z) ∈ 𝔓^{1-r}`, then `z ≡ βy - yβ (mod 𝔓^{1-r})` for some
  `y ∈ 𝔓^1`;
- `b ∈ 𝔓^{-r}` with `s(b) ≡ c (mod 𝔓^{1-r})`.

It produces `γ` with:

1. `γ - (β + b) ∈ 𝔓^{1-r}`;
2. every nonzero element of `F[γ]` is a unit normalizing `𝓛` (`NormalizingUnits`);
3. `F[γ]` and the image of `L` approximate each other at every level (`Approx`, both ways);
4. Claim X: every `y ∈ 𝔓^0` commuting with `β` and `c` is congruent mod `𝔓^1` to some
   `z ∈ 𝔓^0` commuting with `γ`;
5. if `[L:F] = 1`, then `F[γ] = F`.

### Proof

- Take a relative splitting basis `w` (`exists_relSplits_basis`), an index `l₀`, the diagonal
  part `b₁ = σ(b) = Σ_j ε_{j l₀} b ε_{l₀ j}`, and `β₁ = β + b₁`.
- `b₁ ∈ 𝔓^{-r}`, and `β₁` commutes with all matrix units.
- `s` commutes with `σ`: the matrix units commute with `β`, so the bimodule laws apply. Also
  `σ(c) = c`. Hence `s(b₁) - c = σ(s(b) - c) ∈ 𝔓^{1-r}`.
- `refinement_core` then gives the core property for `β₁`. The results of
  `RefinementCentralizer` give (2) and (3) for `F[β₁]`.
- Apply U2 to `z = b - b₁` to get `y ∈ 𝔓^1`, and put `g = 1 + y ∈ U^1(𝔄)`
  (`exists_mem_unitFiltration`). Set `γ = g⁻¹ β₁ g`. Then
  `γ - β₁ = g⁻¹ (β₁ y - y β₁) ≡ βy - yβ ≡ b - b₁ (mod 𝔓^{1-r})`, which gives (1).
- Conjugation by `g` preserves normalizing units (`normalizingUnits_conj`) and approximation
  (`approx_conj_left`, `approx_conj_right`), which gives (2) and (3) for `F[γ]`.
- Claim X. Write `y = Σ_{j,l} ε_{jj} y ε_{ll}`, with blocks `a_{jl} ε_{jl}`. If `a_{jl} ≠ 0`,
  let `d` be the shift of `a_{jl}`. Approximation gives `X_{jl} ∈ F[β₁]` with
  `a_{jl} - X_{jl} ∈ 𝔓^{d+1}`, and `ε_{jl} = a_{jl}⁻¹ · block ∈ 𝔓^{-d}`. So
  `z' = Σ X_{jl} ε_{jl}` commutes with `β₁` and `y - z' ∈ 𝔓^1`. Conjugating by `g` gives `z`.
- The scalar case. The entry map `X ↦ (w_{l₀}`-coordinate of `X(w_{l₀}))` from `F[β₁]` to `L`
  is `F`-linear and injective. It is injective because a nonzero `X` of exact depth `s` would
  satisfy `X ∈ 𝔓^{s+1}` by `sub_entry_mem`. So `[F[β₁]:F] ≤ [L:F] = 1`, `β₁` is a scalar, and
  `γ = β₁`.
