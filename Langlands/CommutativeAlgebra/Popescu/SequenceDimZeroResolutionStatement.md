# Lifting a resolution along a sequence of elements down to dimension zero

`Langlands.CommutativeAlgebra.Popescu.SequenceDimZeroResolutionStatement` (universe `u`).

**Hypotheses.**
- `R` and `Λ` are Noetherian commutative rings, `A` is a finitely presented `R`-algebra,
  `Λ` is an `R`-algebra (all in `Type u`), `f : A →ₐ[R] Λ`, and `q` is a prime ideal of `Λ`.
- `r : ℕ` and `π : Fin r → R`, with `algebraMap R Λ (π i) ∈ q` for all `i`.
- **Annihilators in `R`.** For all `i` and `x ∈ R`: if `π i² · x ∈ (π_j⁸ : j < i)`, then
  `π i · x ∈ (π_j⁸ : j < i)`.
- **Annihilators in `Λ`.** The same with `R` replaced by `Λ` and `π_j` by
  `algebraMap R Λ (π j)`.
- **Strictly standard.** `IsStrictlyStandard R (algebraMap R A (π i))` for all `i`.
- **Bottom condition.** Write `K = Ideal.span {π_i⁸}` in `R`. Let `R₁`, `Λ₁ : Type u` be
  commutative rings with `Λ₁` an `R₁`-algebra, `σ : R →+* R₁` and `τ : Λ →+* Λ₁`
  surjective with `ker σ = K` and `ker τ = K.map (algebraMap R Λ)`, and
  `τ (algebraMap R Λ x) = algebraMap R₁ Λ₁ (σ x)` for all `x ∈ R`. Let `Q` be a prime of `Λ₁`
  with `Q.comap τ = q`, and write `p₁ = Q.comap (algebraMap R₁ Λ₁)`. Then for all such data:
  - `Q ∈ minimalPrimes Λ₁`, and
  - there are a smooth `(R₁)_{p₁}`-algebra `T : Type u` and ring maps `u : A →+* T` and
    `v : T →+* (Λ₁)_Q` with
    `u ∘ algebraMap R A = algebraMap (R₁)_{p₁} T ∘ algebraMap R₁ (R₁)_{p₁} ∘ σ` and
    `v ∘ u = algebraMap Λ₁ (Λ₁)_Q ∘ τ ∘ f`.

Here `(R₁)_{p₁}` and `(Λ₁)_Q` are `Localization.AtPrime`.

**Conclusion.** `CanBeResolved R f q`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`).

- Lemma 9.2 (Tag 07F8, printed p. 22): "Let R → A → Λ ⊃ q be as in Situation 9.1. Let
  r ≥ 1 and π₁, …, π_r ∈ R map to elements of q. Assume (1) for i = 1, …, r we have
  Ann_{R/(π₁⁸, …, π_{i−1}⁸)R}(πᵢ) = Ann_{R/(π₁⁸, …, π_{i−1}⁸)R}(πᵢ²) and
  Ann_{Λ/(π₁⁸, …, π_{i−1}⁸)Λ}(πᵢ) = Ann_{Λ/(π₁⁸, …, π_{i−1}⁸)Λ}(πᵢ²) (2) for
  i = 1, …, r the element πᵢ maps to a strictly standard element in A over R. Then, if
  R/(π₁⁸, …, π_r⁸)R → A/(π₁⁸, …, π_r⁸)A → Λ/(π₁⁸, …, π_r⁸)Λ ⊃ q/(π₁⁸, …, π_r⁸)Λ can be
  resolved, so can R → A → Λ ⊃ q."
- Lemma 9.4 (Tag 07FA, printed p. 23): "Let R → A → Λ ⊃ q be as in Situation 9.1. Let
  p = R ∩ q. Assume (1) q is minimal over h_A, (2) R_p → A_p → Λ_q ⊃ qΛ_q can be resolved,
  and (3) dim(Λ_q) = 0. Then R → A → Λ ⊃ q can be resolved."
- Lemma 11.4 (Tag 07FJ), steps (18) and (20) of its proof (printed pp. 28–31): "(18) It
  suffices to resolve R/I → C ⊗ R/I → Λ/IΛ ⊃ q/IΛ … Ad (18). Follows on applying
  Lemma 9.2 … Ad (20). Apply Lemma 9.4 to the situation in (18). In the rest of the
  arguments the target ring is local Artinian, hence we are looking for a factorization
  by a smooth algebra T over the source ring."

## Encoding and scope

This statement combines Lemma 9.2 with Lemma 9.4 applied to the bottom problem, as
Lemma 11.4 uses them (steps (18) and (20)).

- **Annihilators.** `Ann(πᵢ) ⊆ Ann(πᵢ²)` always holds, so each equality of annihilators is
  the implication stated. The ideal `(π_j⁸ : j < i)` is `Ideal.span` of the image of
  `{j | j < i}`. Indices are zero-based.
- **The bottom problem.** The source hypothesis is that the problem over `R/K` can be
  resolved. Here it is replaced by the hypothesis of Lemma 9.4 for that problem, in the
  form of `LocalDimZeroResolutionStatement` (Lemmas 9.3 and 9.4): `Q` is a minimal prime,
  and `A/KA → (Λ/KΛ)_Q` factors through a smooth algebra over `(R/K)_{p₁}`. The condition
  does not include `h_{A/KA} ⊆ Q`. If that inclusion fails, `A/KA` resolves the bottom
  problem itself; otherwise Lemma 9.4 applies. The factorization is given on `A`: a map out
  of `A/KA = (R/K) ⊗_R A` over `R/K`
  is the same as a map out of `A` compatible with `R → R/K`, which is what the condition on
  `u` says.
- **All models of the quotient.** The bottom condition is required for every pair of
  surjections `σ`, `τ` with the given kernels, not just for the quotient rings `R ⧸ K`
  and `Λ ⧸ KΛ`. These models are all isomorphic, so this is the same condition. It is
  stated this way so that the induction in the proof of Lemma 9.2 can reach the bottom
  through iterated quotients without transporting along isomorphisms.
- **`r = 0`.** The case `r = 0` (with `K = 0`) is allowed. It is then Lemma 9.4 for
  `R → A → Λ ⊃ q` itself.
- **Noetherian `Λ`.** `Λ` is assumed Noetherian, as Lemma 9.4 needs.
- **Relation to the characteristic-zero case.** The hypothesis
  `HasSmoothFactorizations R₁ (Λ₁)_Q` implies the factorization condition, through the
  base change of `R₁ → A/KA` to `(R₁)_{p₁}`. Lemma 11.4 (characteristic `p`) uses the
  weaker form stated here. There the residue field extension of `(R₁)_{p₁} → (Λ₁)_Q` may
  be inseparable, and the proof constructs one smooth algebra `T` for the given `A`
  (steps (22)–(26)) rather than factorizations for all finitely presented algebras.
- `h_A` is `singularRadical R f`, strictly standard elements are `IsStrictlyStandard`, and
  "can be resolved" is `CanBeResolved R f q`; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`.
- **Universe.** All rings are in one universe `u`.
