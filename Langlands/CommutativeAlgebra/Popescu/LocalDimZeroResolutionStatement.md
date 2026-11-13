# Resolving at a minimal prime from a local smooth factorization

`Langlands.CommutativeAlgebra.Popescu.LocalDimZeroResolutionStatement` (universe `u`).

**Hypotheses.**
- `R` and `Λ` are Noetherian commutative rings, `A` is a finitely presented `R`-algebra,
  `Λ` is an `R`-algebra (all in `Type u`), `f : A →ₐ[R] Λ`, and `q` is a prime ideal of `Λ`.
- `singularRadical R f ≤ q`, i.e. `h_A ⊆ q`.
- `q ∈ minimalPrimes Λ`.
- Write `p = q.comap (algebraMap R Λ)` (the prime `R ∩ q`), `R_p = Localization.AtPrime p`
  and `Λ_q = Localization.AtPrime q`. `T : Type u` is a smooth `R_p`-algebra
  (`Algebra.Smooth R_p T`).
- `u : A →+* T` and `v : T →+* Λ_q` are ring maps with
  - `u ∘ algebraMap R A = algebraMap R_p T ∘ algebraMap R R_p`, and
  - `v ∘ u = algebraMap Λ Λ_q ∘ f`.

**Conclusion.** `CanBeResolved R f q`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), printed p. 23.

- Lemma 9.3 (Tag 07F9): "Let R → A → Λ ⊃ q be as in Situation 9.1. Let p = R ∩ q.
  Assume that q is minimal over h_A and that R_p → A_p → Λ_q ⊃ qΛ_q can be resolved.
  Then there exists a factorization A → C → Λ with C of finite presentation such that
  H_{C/R}Λ ⊄ q."
- Lemma 9.4 (Tag 07FA): "Let R → A → Λ ⊃ q be as in Situation 9.1. Let p = R ∩ q.
  Assume (1) q is minimal over h_A, (2) R_p → A_p → Λ_q ⊃ qΛ_q can be resolved, and
  (3) dim(Λ_q) = 0. Then R → A → Λ ⊃ q can be resolved."

Situation 9.1 (Tag 07F7, p. 22): `R` is Noetherian, `A → Λ` is an `R`-algebra map with `A`
of finite presentation, `q ⊂ Λ` is a prime, and `h_A = √(H_{A/R}Λ)`.

## Encoding and scope

This is Lemma 9.4 (with Lemma 9.3, which its proof uses) in the form in which step (20) of
the proof of Lemma 11.4 (Tag 07FJ, printed p. 31) applies it: "In the rest of the
arguments the target ring is local Artinian, hence we are looking for a factorization by
a smooth algebra T over the source ring."

- **Hypothesis (2).** It is replaced by a factorization of `A → Λ → Λ_q` through a smooth
  `R_p`-algebra `T`. This implies (2). The map `u` is compatible with `R → R_p`, so it
  induces `A_p = R_p ⊗_R A → T`. The map `v` agrees with `R → Λ → Λ_q` on `R`, hence on
  `R_p`. Since `T` is smooth (and so finitely presented) over `R_p`, `H_{T/R_p} = T`, and
  `A_p → T → Λ_q` resolves `R_p → A_p → Λ_q ⊃ qΛ_q`. The proof of Lemma 9.3 itself reduces
  to this case: "By our assumption that q is minimal over h_A this means that
  H_{C/R_p}Λ_q = Λ_q. By Lemma 2.8 we may assume that C is smooth over R_p."
- **Ring maps.** `u` and `v` are ring maps with explicit compatibilities, so `T` needs no
  `R`-algebra structure.
- **(1) and (3).** They are encoded as `h_A ⊆ q` and `q ∈ minimalPrimes Λ`. For a minimal
  prime `q` of `Λ`, `h_A ⊆ q` is the same as `q` being minimal over `h_A`. In a Noetherian
  ring, `dim Λ_q = 0` is the same as `q` being a minimal prime.
- **Noetherian `Λ`.** `Λ` is assumed Noetherian. The proof of Lemma 9.4 uses that `Λ_q` is
  Artinian, so that `qΛ_q` is nilpotent.
- **Relation to `DimZeroResolutionStatement`.** This statement implies the Library
  statement `Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionStatement`, which has
  the same data and the hypothesis `HasSmoothFactorizations R Λ_q` in place of the smooth
  `R_p`-algebra `T`. That hypothesis gives the one used here. Apply it to
  `A → Λ → Λ_q` to get a smooth `R`-algebra `T'` with `A → T' → Λ_q`. Then take
  `T = R_p ⊗_R T'`, which is smooth over `R_p` by base change. Let `u` be `A → T' → T`. Let
  `v` be induced by `T' → Λ_q` and `R_p → Λ_q`, which exists because elements of `R \ p`
  map outside `q`, hence to units of `Λ_q`. So a proof of this statement also proves
  `DimZeroResolutionStatement`.
- `h_A` is `singularRadical R f`, and "can be resolved" is `CanBeResolved R f q`; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`.
- **Universe.** All rings are in one universe `u`.
