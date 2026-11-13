# Resolving the local problem at a minimal prime

`Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionStatement` (universe `u`). Let `R`
and `Λ` be Noetherian commutative rings, `A` a finitely presented `R`-algebra, `Λ` an
`R`-algebra (all in `Type u`), `f : A →ₐ[R] Λ` and `q` a prime ideal of `Λ`. Assume

- `singularRadical R f ≤ q`, i.e. `h_A ⊆ q`;
- `q ∈ minimalPrimes Λ`, i.e. `dim Λ_q = 0`;
- `HasSmoothFactorizations R (Localization.AtPrime q)`: every `R`-algebra map from a
  finitely presented `R`-algebra to `Λ_q` factors through a smooth `R`-algebra.

Then `CanBeResolved R f q`.

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

Situation 9.1 (Tag 07F7, p. 22): `R` Noetherian, `A → Λ` an `R`-algebra map with `A` of
finite presentation, `q ⊂ Λ` a prime, `h_A = √(H_{A/R}Λ)`.

## Encoding and scope

This is Lemma 9.4 in the form in which the proof of Lemma 10.3 (Tag 07FE, p. 25)
applies it ("By Lemma 9.4 it suffices to resolve this after localizing at q").

- Hypothesis (2) is replaced by property PT for `R → Λ_q`
  (`HasSmoothFactorizations R (Localization.AtPrime q)`). This implies (2) in the case
  `R = R_p` that Lemma 10.3 uses: the map `A → Λ_q` then factors as `A → C → Λ_q` with `C`
  smooth over `R`, so `H_{C/R} = C`, and `A → C → Λ_q` resolves the localized problem. In
  Lemma 10.3 this hypothesis is obtained from flatness and Proposition 5.3.
- (1) and (3) are encoded as `h_A ⊆ q` and `q ∈ minimalPrimes Λ`. For a minimal prime
  `q` of `Λ`, `h_A ⊆ q` is the same as `q` being minimal over `h_A`, and in a Noetherian
  ring `dim Λ_q = 0` is the same as `q` being a minimal prime.
- `Λ` is assumed Noetherian. The proof of Lemma 9.4 uses that `Λ_q` is Artinian, so that
  `qΛ_q` is nilpotent; in Lemma 10.3, `Λ` is Noetherian.
- `h_A` is `singularRadical R f`, and "can be resolved" is `CanBeResolved R f q`; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`. `Λ_q` is
  `Localization.AtPrime q` with its `R`-algebra structure through `Λ`.
- All rings are in one universe `u`.
