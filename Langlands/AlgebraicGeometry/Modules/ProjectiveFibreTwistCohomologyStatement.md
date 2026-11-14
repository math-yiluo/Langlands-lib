# Cohomology of large twists on the fibres of a projective flat family

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyStatement` defines
the twist notation `twist` and the proposition `ProjectiveFibreTwistCohomologyStatement`. It uses
the fibre notation of `ProperFlatFibreCohomologySemicontinuityStatement` (same namespace):
`fibreCohomology g t F p = Hᵖ(Y_t, F_t)` over `κ(t)`, and
`fibreEulerCharacteristic g t F = χ(F_t)`.

## Twists

For modules `𝓛` and `F` on a scheme, `twist 𝓛 F n` is `F ⊗ 𝓛^{⊗ n}` with right-associated tensor
products of the FLT port (`AlgebraicGeometry.Scheme.Modules.monoidalCategory`): `twist 𝓛 F 0 = F`
and `twist 𝓛 F (n + 1) = twist 𝓛 F n ⊗ 𝓛`. With `𝓛` the pullback of `𝓛X` to `X_T`, this is
definitionally the twist `L(m)` written with `Nat.rec` in `PicardHilbertPolynomialPiecesStatement`.

## The statement

Let `A` be a noetherian ring, `f : X ⟶ Spec A` proper and flat, and `𝓛X` an invertible module on
`X` with a projective presentation `𝔓 : 𝓛X.ProjPresentation f N` whose morphism
`𝔓.toProj : X ⟶ ℙᴺ_A` is a closed immersion. So `𝓛X = O_X(1)` for a closed embedding of `X` into
`ℙᴺ_A`. Let `T` be locally noetherian, `s : T ⟶ Spec A`, and `F` an invertible module on
`X_T = pullback f s`. Write `𝓛` for the pullback of `𝓛X` to `X_T` and `F(n) = twist 𝓛 F n`. For
the fibres `X_t` of `pullback.snd f s : X_T ⟶ T`:

1. **Uniform vanishing.** Every point of `T` has an open neighbourhood `V` and an `n₀` such that
   `Hᵖ(X_{t'}, F(n)_{t'}) = 0` for all `t' ∈ V`, all `n ≥ n₀` and all `p > 0`.
2. **Sections.** If the fibre `X_t` is nonempty, there is `n₀` with `H⁰(X_t, F(n)_t) ≠ 0` for all
   `n ≥ n₀`.
3. **Polynomiality.** For every `t` there is a rational polynomial `P` of degree at most `N` with
   `χ(F(n)_t) = P(n)` for all `n ∈ ℕ`.

## Sources and provenance

All three clauses are derived (standard consequences) from the following sources.

- The Stacks Project (literature id `stacks-projective-cohomology-ample-2026-11-13`, a folder with
  the HTML pages and text aids of the cited tags):
  - Lemma 30.16.2 (Tag 02O1, file `02O1.html`): if `S` is noetherian, `f : X → S` proper, `F`
    coherent and `L` relatively ample, then `Rᵖ f_*(F ⊗ L^{⊗ n}) = 0` for `p > 0` and `n ≥ n₀`.
  - Proposition 28.27.13(7) (Tag 01Q3, file `01Q3.html`): on a quasi-compact scheme with an ample
    `L`, every quasi-coherent `F` of finite type has `F ⊗ L^{⊗ n}` globally generated for all
    large `n`.
  - Lemma 33.45.1 (Tag 0BEM, file `0BEM.html`): for a proper scheme over a field, a coherent `F`
    and an invertible `L`, `n ↦ χ(F ⊗ L^{⊗ n})` is a numerical polynomial of degree at most
    `dim Supp F`.
- D. Mumford, *Abelian Varieties*, Chapter II, §5 (literature id
  `mumford-abelian-varieties-chapter-ii-scan`), Corollary 4, printed p.53 (retained PDF page 8):
  with `f : X → Y` proper, `Y` noetherian and `F` coherent and flat over `Y`, if `Rᵏ f_*(F) = 0`
  for `k > k₀`, then `Hᵏ(X_y, F_y) = 0` for all `y ∈ Y` and `k > k₀`.

Derivations:

- Clause 1: take an affine noetherian open `V = Spec B` around the point. Over `V`, `X_T` is
  proper over `Spec B`, and the pullback of `𝓛X` is relatively ample: it is the pullback of
  `O(1)` along the closed immersion obtained by base change of `𝔓.toProj`. Each `F(n)` is
  invertible on `X_T`, which is flat over `T`, so `F(n)` is coherent and flat over `V`. Tag 02O1
  gives `n₀` with `Rᵖ f_*(F(n)) = 0` over `V` for `p > 0` and `n ≥ n₀`. Mumford's Corollary 4 with
  `k₀ = 0` then gives the vanishing on every fibre over `V`.
- Clause 2: on the nonempty fibre `X_t`, which is proper over `κ(t)` (hence quasi-compact), the
  pullback of `𝓛X` is ample, as the pullback of `O(1)` under a closed immersion into `ℙᴺ_{κ(t)}`.
  Tag 01Q3(7) makes `F(n)_t` globally generated for large `n`. A globally generated invertible
  module on a nonempty scheme has a nonzero global section, and `H⁰` is global sections.
- Clause 3: Tag 0BEM on the proper `κ(t)`-scheme `X_t`, applied to the invertible `F_t` and the
  pullback of `𝓛X`. Here `F(n)_t ≅ F_t ⊗ 𝓛_t^{⊗ n}` because pullback is monoidal. The degree is at
  most `dim X_t ≤ N`, since `X_t` is a closed subscheme of `ℙᴺ_{κ(t)}`.

Kleiman, *The Picard scheme* (literature id `kleiman-2005-picard-scheme-arxiv-math0504020v1`,
proof of Theorem 4.8, pp.28–30) uses these facts for the pieces `P^φ_m`. The statement is a
prerequisite of a proof of `PicardHilbertPolynomialPiecesStatement` (Task 6028).
