# Resolution of the local problem in characteristic zero

`Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionStatement` (universe `u`): let
`k` be a field of characteristic zero, `A` a finitely presented `k`-algebra, `Λ` a
Noetherian `k`-algebra (all in `Type u`), `f : A →ₐ[k] Λ` a `k`-algebra map and `q` a
prime ideal of `Λ`. If `q ∈ (singularRadical k f).minimalPrimes` and the localization
`Λ_q` is a regular local ring, then `CanBeResolved k f q`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 10.3 (Tag 07FE, printed
pp. 24-25): "Let k → A → Λ ⊃ q be as in Situation 9.1 where (1) k is a field, (2) Λ is
Noetherian, (3) q is minimal over h_A, (4) Λ_q is a regular local ring, and (5) the
field extension κ(q)/k is separable. Then k → A → Λ ⊃ q can be resolved."
Situation 9.1 (Tag 07F7, p. 22): `R` Noetherian, an `R`-algebra map `A → Λ` with `A`
finitely presented, and a prime `q ⊂ Λ`; `h_A = √(H_{A/R}Λ)`.

## Encoding and scope

- This is the special case of Lemma 10.3 in which `k` has characteristic zero
  (`[CharZero k]`). In characteristic zero every field extension is separable, so
  hypothesis (5) holds automatically and is omitted. This is the only case in which
  Theorem 12.1 (Tag 07GC) invokes Lemma 10.3 ("If the characteristic of k is zero,
  this follows from Lemma 10.3"); the general separable case is not stated here.
- (3) "q is minimal over h_A" is `q ∈ (singularRadical k f).minimalPrimes`, with
  `singularRadical k f = h_A` (see `Langlands/CommutativeAlgebra/Popescu/Basic.md`).
- (4) is `IsRegularLocalRing (Localization.AtPrime q)` (Mathlib).
- "Can be resolved" is `CanBeResolved k f q` (text after Situation 9.1).
