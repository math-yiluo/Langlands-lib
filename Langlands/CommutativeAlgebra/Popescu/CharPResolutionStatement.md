# Resolution of the local problem in positive characteristic

`Langlands.CommutativeAlgebra.Popescu.CharPResolutionStatement` (universe `u`): let `k`
be a field of characteristic `p` for a prime `p`, `A` a finitely presented `k`-algebra
and `Λ` a `k`-algebra with `GeometricallyRegular k Λ` (all in `Type u`). For every
`k`-algebra map `f : A →ₐ[k] Λ` and prime `q` of `Λ` with
`q ∈ (singularRadical k f).minimalPrimes`, `CanBeResolved k f q` holds.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.4 (Tag 07FJ, printed p. 28):
"Let k → A → Λ ⊃ q be as in Situation 9.1 where (1) k is a field of characteristic
p > 0, (2) Λ is Noetherian and geometrically regular over k, (3) q is minimal over h_A.
Then k → A → Λ ⊃ q can be resolved." Situation 9.1 (Tag 07F7, p. 22): `R` Noetherian,
an `R`-algebra map `A → Λ` with `A` finitely presented, and a prime `q ⊂ Λ`.

## Encoding

- (1): `p : ℕ` with `[Fact p.Prime]` and `[CharP k p]` (the characteristic of a field
  is zero or prime, so "characteristic p > 0" means a prime `p`).
- (2): the Library predicate `Langlands.CommutativeAlgebra.GeometricallyRegular k Λ`,
  which includes that `Λ` is Noetherian.
- (3): `q ∈ (singularRadical k f).minimalPrimes`, with `singularRadical k f = h_A`
  (see `Langlands/CommutativeAlgebra/Popescu/Basic.md`); `[q.IsPrime]` is also supplied.
- "Can be resolved" is `CanBeResolved k f q` (text after Situation 9.1).
