# Proof: regular local rings are domains

This module proves the Library proposition
`Langlands.CommutativeAlgebra.RegularLocalDomainStatement.{u}` from
`Langlands.CommutativeAlgebra.RegularLocalDomainStatement`:

```lean
theorem regularLocalDomain : RegularLocalDomainStatement.{u}
```

That is, for every commutative ring `R : Type u` with `IsRegularLocalRing R`,
`R` is a domain. No hypotheses are used beyond those in the statement. The
module imports only the statement module and
`Mathlib.RingTheory.KrullDimension.Regular`.

## Provenance and route

The statement is Stacks Project Lemma 10.106.2 (Tag 00NP). The Stacks proof
uses the Krull intersection theorem and Lemma 10.106.1 (Tag 00NO), which
identifies the associated graded ring `⊕ m^n/m^{n+1}` with a polynomial ring
over the residue field. Mathlib at the pinned commit has no such
identification, so this proof does not follow the Stacks route. It also does
not use the shortcut that maps `R` into its associated graded ring, which the
Stacks maintainers rejected in Comment #9238 on Tag 00NP (see the statement's
Markdown).

Instead the proof uses the classical induction on the minimal number of
generators of the maximal ideal `m`. It takes `x ∈ m` outside `m²` and outside
every minimal prime, shows that `R/(x)` is again regular with one generator
fewer, and lifts the domain property from `R/(x)` to `R` with Nakayama's lemma.
The argument and its Lean arrangement were written for this module; every
other ingredient comes from Mathlib.

## Auxiliary lemmas

All are in the namespace `Langlands.CommutativeAlgebra.RegularLocalDomain`, for
a commutative ring `R` in any universe. Write `m` for `maximalIdeal R`.

- `spanFinrank_maximalIdeal_quotient_add_one_le`: let `R` be a Noetherian
  local ring, `x ∈ m` with `x ∉ m ^ 2`, and assume an instance
  `IsLocalRing (R ⧸ Ideal.span {x})`. Then
  `(maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ m.spanFinrank`.
  The proof works in the cotangent space `CotangentSpace R = m/m²` over the
  residue field `k`.
  1. The image `v` of `x` is nonzero because `x ∉ m²`
     (`Ideal.toCotangent_eq_zero`). So the line `K = k ∙ v` has dimension `1`,
     and `dim (m/m² ⧸ K) + 1 = dim m/m²` (`Submodule.finrank_quotient_add_finrank`).
  2. Lift a basis `b` of `m/m² ⧸ K` to elements `y i ∈ m`, using
     `Function.surjInv` for the surjection `m → m/m² → (m/m²)/K`.
  3. The set `{x} ∪ {y i}` spans `m`. By
     `IsLocalRing.CotangentSpace.span_image_eq_top_iff` it suffices that its
     image spans `m/m²`. That span `U` contains `K`, and its image in the
     quotient by `K` contains the basis `b`. So `U ⊔ K = U` is everything
     (`Submodule.map_mkQ_eq_top`).
  4. Mapping to `R ⧸ (x)` (`IsLocalRing.map_maximalIdeal_of_surjective`) and
     dropping the image of `x`, which is `0`, shows that the maximal ideal of
     `R ⧸ (x)` is spanned by the images of the `y i`. Hence its `spanFinrank`
     is at most `dim (m/m² ⧸ K)`
     (`Submodule.spanFinrank_span_le_ncard_of_finite`).
  5. `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` turns
     `dim m/m²` into `m.spanFinrank`, and `omega` concludes.
- `exists_mem_maximalIdeal_avoiding` (prime avoidance): in a Noetherian local
  ring, if `m ≠ m ^ 2` and `m` is not a minimal prime, then some `x ∈ m` lies
  neither in `m ^ 2` nor in any minimal prime. The family
  `{m ^ 2} ∪ minimalPrimes R` is finite
  (`minimalPrimes.finite_of_isNoetherianRing`), and every member other than
  `m ^ 2` is prime. Mathlib's prime avoidance lemma
  `Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite` allows up to two
  non-prime proper members `a` and `b`; here both are `m ^ 2`, which is proper
  because `m ^ 2 ≤ m`. The lemma says that `m` lies in the union only if `m`
  is one of the members. Both cases are excluded by the hypotheses.
- `isDomain_of_isPrime_span_singleton`: in a Noetherian local ring, if `x ∈ m`
  lies in no minimal prime and `Ideal.span {x}` is prime, then `R` is a domain.
  Take a minimal prime `p ⊆ (x)` (`Ideal.exists_minimalPrimes_le`). For
  `y ∈ p` write `y = r * x`. Then `r ∈ p` because `p` is prime and `x ∉ p`.
  So `p ≤ m • p`, and Nakayama's lemma
  (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, with `m` inside the
  Jacobson radical and `p` finitely generated) gives `p = ⊥`. Hence `⊥` is
  prime and `R` is a domain (`IsDomain.of_bot_isPrime`).

## Main induction

`isDomain_of_spanFinrank_eq (n : ℕ)`: every `R : Type u` with
`[CommRing R] [IsRegularLocalRing R]` and `m.spanFinrank = n` is a domain. The
proof is by strong induction on `n` (`Nat.strong_induction_on`). Regularity
gives `(m.spanFinrank : WithBot ℕ∞) = ringKrullDim R`.

1. **`n = 0`.** Then `m = ⊥` (`Submodule.spanFinrank_eq_zero_iff_eq_bot`, as
   `m` is finitely generated). So `⊥` is the maximal ideal, hence prime, and
   `R` is a domain.
2. **`n > 0`: `m ≠ m ^ 2`.** Otherwise `m ≤ m • m`, and Nakayama's lemma gives
   `m = ⊥`, so `spanFinrank m = 0` (`Submodule.spanFinrank_bot`), a
   contradiction.
3. **`m` is not a minimal prime.** Otherwise `m.height = 0`
   (`Ideal.height_eq_zero_iff`). By
   `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`, the Krull dimension is
   then `0`, so `n = 0`, a contradiction.
4. **Choice of `x`.** `exists_mem_maximalIdeal_avoiding` gives `x ∈ m` with
   `x ∉ m ^ 2` and `x` in no minimal prime. Since `x` is not a unit,
   `Ideal.span {x} ≠ ⊤`, so `R ⧸ (x)` is nontrivial
   (`Ideal.Quotient.nontrivial_iff`), and it is local as a quotient of a local
   ring (`IsLocalRing.of_surjective'`).
5. **`R ⧸ (x)` is regular.** Write `S = R ⧸ (x)`. The first auxiliary lemma
   gives `spanFinrank m_S + 1 ≤ n`. Krull's height theorem in the form
   `Ideal.height_le_ringKrullDim_quotient_add_one`, applied to `m` and `x ∈ m`,
   together with `maximalIdeal_height_eq_ringKrullDim`, gives
   `ringKrullDim R ≤ ringKrullDim S + 1`. As `S` is nontrivial,
   `ringKrullDim S` is not `⊥` (`ringKrullDim_nonneg_of_nontrivial`), so it
   equals `d` for some `d : ℕ∞` (`WithBot.ne_bot_iff_exists`). Chaining the two
   inequalities gives `spanFinrank m_S + 1 ≤ d + 1` in `ℕ∞`. Cancelling `1`
   (`ENat.add_le_add_iff_right`) gives `spanFinrank m_S ≤ ringKrullDim S`, and
   `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` makes `S` regular. `S`
   lives in the same universe `u`, as the induction requires.
6. **Induction and lift.** Since `spanFinrank m_S < n`, the induction
   hypothesis shows that `S` is a domain. By `Ideal.Quotient.isDomain_iff_prime`
   the ideal `(x)` is prime. `isDomain_of_isPrime_span_singleton` then shows
   that `R` is a domain.

Finally, `regularLocalDomain` introduces `R` and the regularity hypothesis and
applies `isDomain_of_spanFinrank_eq` with `n = m.spanFinrank`.
