# Rank of the actual prime-adic Tate module at a geometric point

`Langlands.AbelianScheme.Tate.PrimeAdic.geometricPrimeAdicRank` proves
exactly the published proposition `GeometricPrimeAdicRankStatement.{u}`
from [`GeometricPrimeAdicRankStatement`](GeometricPrimeAdicRankStatement.md).
Let `S` be a scheme, `A : AbelianScheme S` with
`A.HasRelativeDimension g`, and `p` a prime invertible in `Γ(S, ⊤)`. For
every algebraically closed field `Ω : Type u` and point
`s : Spec Ω ⟶ S`, the theorem gives a `ℤ_[p]`-linear equivalence
`(Fin (2 * g) → ℤ_[p]) ≃ₗ[ℤ_[p]] IntegralAt A p s`. It also proves that
`RationalAt A p s` is finite-dimensional over `ℚ_[p]` with `finrank`
equal to `2 * g`. The universe `u` is arbitrary. The theorem adds no
hypotheses to the unchanged statement and includes `g = 0`.

## Implemented proof

The proof has two steps.

1. The published finite-level theorem
   `Langlands.AbelianScheme.Tate.geometricTorsionRank` from
   [`GeometricTorsionRankProof`](GeometricTorsionRankProof.md) is applied
   at every level `p ^ n`. Positivity is `pow_pos` of the prime, and
   invertibility of `(p ^ n : Γ(S, ⊤))` follows from the hypothesis on
   `p` by `Nat.cast_pow` and `IsUnit.pow`. For every `n` this gives a
   `ZMod (p ^ n)`-linear equivalence from `Fin (2 * g) → ZMod (p ^ n)` to
   the actual level `GroupScheme.Tate.Level A.toGrp (Over.mk s) (p ^ n)`.
   It also gives the cardinality `(p ^ n) ^ (2 * g)` of that level.
2. The generic theorems of [`PrimeAdicFreeness`](PrimeAdicFreeness.md),
   with `r = 2 * g`, turn these level facts into the conclusions.
   `integral_linearEquiv_of_level` gives the integral equivalence. It
   proves that the successive transitions are surjective by counting
   points. It then chooses residue bases compatible across all levels by
   Kőnig's lemma and assembles their coordinates into p-adic integers.
   `rational_finrank_of_linearEquiv` applied to that equivalence gives
   finite-dimensionality and the rank of the rational module, by base
   change of a free module.

`IntegralAt A p s` and `RationalAt A p s` are reducible abbreviations for
`GroupScheme.Tate.PrimeAdic.Integral A.toGrp (Over.mk s) p` and the
corresponding `Rational`. So the generic theorems apply to them directly.

## Provenance and scope

The source is Edixhoven–van der Geer–Moonen, *Abelian Varieties*
(preliminary draft built 2012-02-08), Chapter X (10.1)–(10.3), printed
pp.141–142. The source correspondence and the relative geometric-point
specialization are in the statement's companion. This module is a derived
composition: the passage to the field fibre, the transfer of the unit
condition, and the finite-level rank and cardinality all come from the
published `geometricTorsionRank`. The inverse-limit step is the internal
argument of `PrimeAdicFreeness`, which need not follow the source's
route.

The equivalence is chosen noncanonically. No continuity, Galois or
monodromy compatibility, Weil pairing, or statement at the characteristic
prime is asserted.

The independently accepted proof by Worker 3366 proves this same statement.
Its distinct generic construction is retained in
[PrimeAdicCoordinates](PrimeAdicCoordinates.md), imported here, with its original
`GeometricRank` namespace. The two contributions share this single geometric
theorem and the rational-rank theorem, with unchanged hypotheses and conclusions.
