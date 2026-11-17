# Separating group-ring elements by the quotients `Λ ⧸ nΛ`

Worker 732.

Module `Langlands.GroupScheme.Torus.TorsionDensityLattice`. This is an internal helper
module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDensityStatement`
([statement](MultiplicativeTypeTorsionDensityStatement.md),
[proof](MultiplicativeTypeTorsionDensityProof.md)). It contains only algebra about
finitely generated abelian groups and their monoid algebras. It adds no axioms and no
`sorry`. Every declaration is in the namespace `Langlands.GroupScheme.TorsionDensity`.

## Purpose

Milne proves the density theorems 12.32 and 12.33 by showing that an element of the
coordinate ring of `G` that vanishes on every `G_n` is zero. For the diagonalizable group
`D(Λ) = Spec R[Λ]`, the subgroup `G_n` is `D(Λ ⧸ nΛ)`. Its coordinate ring is `R[Λ ⧸ nΛ]`,
and restriction to `G_n` is the map `R[Λ] → R[Λ ⧸ nΛ]` induced by the quotient map
`Λ → Λ ⧸ nΛ`. (This identification is motivation only. The Lean proof never constructs
`G_n`. It uses only that the point `Spec R[Λ ⧸ nΛ] → D(Λ)` is `n`-torsion; see
[`DiagonalizableTorsionDensity`](DiagonalizableTorsionDensity.md).) This module proves
the algebraic fact behind this argument: once `n` is a
large enough multiple of a fixed `N > 0`, this map sends a given nonzero element to a
nonzero element. This is derived content and is not a numbered result of the source.

## Declarations

- `multiples Λ n : AddSubgroup Λ` (an `abbrev`) is the subgroup `nΛ`, the range of the
  homomorphism `x ↦ n • x`. `mem_multiples` says `d ∈ nΛ ↔ ∃ x, n • x = d`.
  `nsmul_mem_multiples` says `n • x ∈ nΛ`.

- `exists_bound_of_ne_zero b hd`. Let `b : Λ ≃+ (I → ℤ) × A` with `I` finite (a `Fintype`)
  and `A` an abelian group. For every nonzero `d : Λ` there is `M` such that `d ∉ nΛ`
  whenever `Nat.card A ∣ n` and `M < n`.
  *Proof.* Take `M = ∑ i, |(b d).1 i|`. Suppose `d = n • x`. Then `n • (b x).2 = 0`,
  because `Nat.card A` divides `n` (Mathlib's `card_nsmul_eq_zero'`). So `(b d).2 = 0`.
  Also `(b d).1 i = n * (b x).1 i` for each `i`. If some `(b x).1 i ≠ 0`, then
  `|(b d).1 i| ≥ n > M ≥ |(b d).1 i|`, a contradiction. So `(b x).1 = 0`, hence
  `b d = 0` and `d = 0`. (If `A` is infinite, then `Nat.card A = 0` and the conclusion is
  vacuous.)

- `exists_bound_injOn b s`. For a finite set `s : Finset Λ` there is `M` such that the
  quotient map `Λ → Λ ⧸ nΛ` is injective on `s` whenever `Nat.card A ∣ n` and `M < n`.
  *Proof.* Use `choose` to get a bound `M d` from `exists_bound_of_ne_zero` for each
  nonzero `d`, and take the bound `0` for `d = 0`. Let `M` be the supremum of
  `M (a - c)` over pairs `(a, c) ∈ s ×ˢ s`. If `a ≠ c` in `s` have the same image, then
  `a - c ∈ nΛ` (`QuotientAddGroup.eq_iff_sub_mem`), which contradicts the bound for
  `a - c`.

- `eq_zero_of_mapDomain_eq_zero q f hq h`. Let `R` be a semiring and
  `f : AddMonoidAlgebra R α`. Suppose `q : α → β` is injective on the support of `f` and
  `AddMonoidAlgebra.mapDomain q f = 0`. Then `f = 0`.
  *Proof.* The coefficients of `mapDomain q f` are `Finsupp.mapDomain q f.coeff`. For
  `a` in the support, Mathlib's `Finsupp.mapDomain_apply'` gives the coefficient of `q a`
  as `f.coeff a`. So every coefficient of `f` vanishes.

- `exists_separating Λ` (main result). Let `Λ : Type u` be a finitely generated abelian
  group (`AddGroup.FG Λ`). There is `N : ℕ` with:
  1. `0 < N`;
  2. every prime `p` dividing `N` is the order of a nonzero element of `Λ`: there is
     `x ≠ 0` with `p • x = 0`;
  3. for every semiring `R : Type v` and every nonzero `f : AddMonoidAlgebra R Λ`, there is
     `M` such that `AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' (multiples Λ n)) f ≠ 0`
     for every multiple `n` of `N` with `M < n`.

  *Proof.* The published `Diagonalizable.exists_freeFiniteEquiv` (module
  [`Torus.DiagonalizablePowerDecomposition`](DiagonalizablePowerDecomposition.md)) gives
  `Λ ≃+ (I → ℤ) × A` with `I` finite and `A` a finite abelian group. Take
  `N = Nat.card A`, which is positive. For a prime `p ∣ N`, Cauchy's theorem (Mathlib's
  `exists_prime_addOrderOf_dvd_card'`) gives `a ∈ A` of order `p`. Then
  `x = b⁻¹ (0, a)` is nonzero and `p • x = 0`. For the separation, apply
  `exists_bound_injOn` to the support of `f` and then `eq_zero_of_mapDomain_eq_zero`.

Property 2 is used in part 2 of the theorem. There `N` must be prime to the
characteristic exponent `p` of `k`, and a smooth `G` has no `p`-torsion in its character
group.

## Source

The method is Milne's, from the proofs of Theorems 12.32 and 12.33 of *Algebraic Groups*
(2017), source ID `milne-2017-algebraic-groups`, pp. 242–243. There, after a reduction to
an algebraically closed field, `G` is written as a product of copies of `𝔾_m` and a finite
group, and the argument shows that a function vanishing on every `G_n` is zero. This
module proves the corresponding fact directly for the group algebra `R[Λ]` over any
semiring `R`, using the decomposition `Λ ≃ ℤ^I × A`.
