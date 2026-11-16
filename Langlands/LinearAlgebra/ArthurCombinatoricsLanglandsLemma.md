# Langlands' combinatorial lemma

Author: Worker 3657.

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsLanglandsLemma`. It
imports `Langlands.LinearAlgebra.ArthurCombinatoricsSigma`, changes no
published file and states no new proposition.

It is part of the proof of
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (Task 7174) and
proves the conjunct

```lean
theorem Langlands.ArthurCombinatorics.langlandsCombinatorialLemmaStatement :
    LanglandsCombinatorialLemmaStatement.{u}
```

## Notation

For `Θ_Q ⊆ Θ_P ⊆ b.support`, `Λ ∈ M` and `H ∈ N`, write
`c_i = corootValue P Θ_Q Λ i` (Arthur's `Λ(α^∨)` for the root `α ∈ Δ_Q^P`
attached to `i ∈ Θ_P \ Θ_Q`), `I(X, Y) = {Θ : X ⊆ Θ ⊆ Y}`,
`s(Θ₁) = (−1)^{|Θ_P \ Θ₁|}`, and

- `F(Θ_P) = ∑_{Θ_R ∈ I(Θ_Q, Θ_P)} ε_Q^R(Λ) φ_Q^R(Λ, H) τ_R^P(H)`, the
  left-hand side of the lemma;
- `g(Θ₁) = 0` if `c_i ≤ 0` for some `i ∈ Θ₁ \ Θ_Q`, and `1` otherwise, the
  right-hand side of the lemma for `Θ₁` in place of `Θ_P`.

The numbers `c_i` depend only on `Θ_Q`, not on `Θ_R` or `Θ_P`. This is why
the same `g` serves for all `Θ₁`.

## Auxiliary results

- `tau_self`, `tauHat_self`: `τ_P^P = 1` and `τ̂_P^P = 1` (empty conditions).
- `tau_eq_neg_sum` (the remark after Arthur's Corollary 6.2, solved for
  `τ_R^P`): for `Θ_R ⊊ Θ_P ⊆ b.support`,
  `τ_R^P(H) = −∑_{Θ₁ ∈ I(Θ_R, Θ_P), Θ₁ ≠ Θ_P} s(Θ₁) τ_R^{Θ₁}(H) τ̂_{Θ₁}^P(H)`.
  `tauTauHat_sum_eq_sigma` and `sigma_self_eq_zero` (module
  `ArthurCombinatoricsSigma`) give
  `∑_{Θ₁ ∈ I(Θ_R, Θ_P)} s(Θ₁) τ_R^{Θ₁} τ̂_{Θ₁}^P = 0`. The term `Θ₁ = Θ_P` of
  this sum is `τ_R^P`.
- `epsilon_mul_phi_eq_sum` (Arthur's "(6.2) equals (6.4)"): for
  `Θ_Q ⊆ Θ_P`,
  `ε_Q^P(Λ) φ_Q^P(Λ, H) = ∑_{Θ₁ ∈ I(Θ_Q, Θ_P)} s(Θ₁) τ̂_{Θ₁}^P(H) g(Θ₁)`.
  Put `L = Θ_Λ = {i ∈ Θ_P : i ∈ Θ_Q or c_i > 0}` (Arthur's `P_Λ`) and
  `A = Θ_Q ∪ {i ∈ Θ_P : ϖ^P_i(H) ≤ 0}`. For `Θ₁ ∈ I(Θ_Q, Θ_P)`,
  `τ̂_{Θ₁}^P(H) = [A ⊆ Θ₁]` and `g(Θ₁) = [Θ₁ ⊆ L]`. So the right-hand side is
  `∑_{A ⊆ Θ₁ ⊆ L} (−1)^{|Θ_P \ Θ₁|}`. By `alternatingSum_eq` this is
  `(−1)^{|Θ_P \ L|}` if `A = L` and `0` otherwise. On the left,
  `{i ∈ Θ_P \ Θ_Q : c_i ≤ 0} = Θ_P \ L`, so `ε_Q^P(Λ) = (−1)^{|Θ_P \ L|}`.
  The condition defining `φ_Q^P(Λ, H)` says that for `i ∈ Θ_P \ Θ_Q`,
  `ϖ^P_i(H) ≤ 0` exactly when `c_i > 0`. That is `A = L`, so
  `φ_Q^P(Λ, H) = [A = L]`.

## The lemma: `langlandsCombinatorial_eq`

`F(Θ_P) = g(Θ_P)` for all `Θ_P` with `Θ_Q ⊆ Θ_P ⊆ b.support`. The proof is by
strong induction on the finite set `Θ_P` (`Finset.strongInduction`), with
`Θ_Q`, `Λ` and `H` fixed. The induction hypothesis is used only for
`Θ_Q ⊆ Θ₁ ⊊ Θ_P`.

1. Split off the term `Θ_R = Θ_P` of `F(Θ_P)`. It is `ε_Q^P φ_Q^P`, since
   `τ_P^P = 1`.
2. For `Θ_R ≠ Θ_P`, replace `τ_R^P` by `tau_eq_neg_sum`. Exchanging the two
   sums (`Finset.sum_comm'`; the pairs are those with
   `Θ_Q ⊆ Θ_R ⊆ Θ₁ ⊊ Θ_P`) gives
   `∑_{Θ_R ≠ Θ_P} ε φ τ_R^P = −∑_{Θ₁ ∈ I(Θ_Q, Θ_P), Θ₁ ≠ Θ_P} s(Θ₁) τ̂_{Θ₁}^P(H) F(Θ₁)`.
   This is Arthur's `−(6.3)`.
3. By the induction hypothesis, `F(Θ₁) = g(Θ₁)` for these `Θ₁`.
4. By `epsilon_mul_phi_eq_sum`, with its term `Θ₁ = Θ_P` (equal to `g(Θ_P)`)
   split off,
   `ε_Q^P φ_Q^P = g(Θ_P) + ∑_{Θ₁ ≠ Θ_P} s(Θ₁) τ̂_{Θ₁}^P(H) g(Θ₁)`.
5. Adding 1 and 2 leaves `F(Θ_P) = g(Θ_P)`.

`langlandsCombinatorialLemmaStatement` is `langlandsCombinatorial_eq` at
universe `u`.

## Provenance

`LanglandsCombinatorialLemmaStatement` is Arthur, *A trace formula for
reductive groups I* (1978), Lemma 6.3, p.940, with its proof on pp.940–941
(registered as `arthur-1978-trace-formula-reductive-groups-I`; PDF page =
printed page − 910, so PDF pages 30–31). The definitions of `ε_Q^P(Λ)` and
`φ_Q^P(Λ, H)` precede the lemma on p.940. Arthur attributes the lemma to
Langlands for `Λ` and `H` in general position and proves it in general from
Proposition 1.1.

The Lean proof follows Arthur's: the remark after Corollary 6.2 (p.940), the
split into (6.2) and (6.3), the induction hypothesis, and the identification
of (6.2) with (6.4). There are two differences.

- Arthur inducts on `dim(A_0/A_P)`. The Lean proof uses strong induction on
  `Θ_P`, as the task contract allows.
- Arthur's last step is "(6.2) equals (6.4)", which he calls "a consequence
  of Proposition 1.1 and the definitions". The Lean proof writes this out as
  `epsilon_mul_phi_eq_sum`.

## Axioms

The module compiles without errors or warnings (`lean_check` bd364ddb). The
lake-build inspection c476c2ed (over Library `72480b70`) of `arthurCombinatoricsStatement`, which
depends on `langlandsCombinatorialLemmaStatement`, reports only `propext`,
`Classical.choice` and `Quot.sound`.
