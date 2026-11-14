# A unit product from a generating family over a semilocal ring

This module proves two lemmas about a commutative ring `R` with finitely many maximal ideals.
Here this means `Finite (MaximalSpectrum R)`. Both lemmas are in namespace
`Langlands.Algebra.Semilocal`, with `R` and `S` in one universe `u`. They are helpers for
`Langlands.Algebra.UnitCocycleSemilocal`, which uses them to trivialise unit cocycles over a
semilocal base. That is the Hilbert 90 step in the proof of
`Langlands.GroupScheme.InducedTorusQuotientPointSurjectivityStatement`.

## Provenance

Both lemmas are internal and derived. They are the usual prime-avoidance and
Chinese-remainder argument for semilocal rings, which also shows that an invertible module
over a semilocal ring is free. Here the argument is phrased for two submodules whose products
come from `R`, because the next module needs exactly this form.

## `exists_separating`

```text
theorem exists_separating [Finite (MaximalSpectrum R)] (P : MaximalSpectrum R) :
    ∃ e : R, e ∉ P.asIdeal ∧ ∀ Q : MaximalSpectrum R, Q ≠ P → e ∈ Q.asIdeal
```

For every maximal ideal `P`, some element lies outside `P` and inside every other maximal
ideal.

*Proof.* Let `s` be the finite set of maximal ideals other than `P`. The product of the
ideals in `s` is not contained in `P`. If it were, then since `P` is prime
(`Ideal.IsPrime.prod_le`), some `Q ∈ s` would satisfy `Q ≤ P`, and maximality of `Q` would
force `Q = P`. Choose `e` in the product but not in `P`. The product is contained in the
infimum of the ideals in `s` (`Ideal.prod_le_inf`), so `e` lies in every `Q ≠ P`.

## `exists_isUnit_of_span_eq_top`

```text
theorem exists_isUnit_of_span_eq_top [Finite (MaximalSpectrum R)]
    (hinj : Function.Injective (algebraMap R S)) (M M' : Submodule R S)
    (hprod : ∀ m ∈ M, ∀ m' ∈ M', ∃ r : R, algebraMap R S r = m * m')
    (hspan : Ideal.span {r : R | ∃ m ∈ M, ∃ m' ∈ M', algebraMap R S r = m * m'} = ⊤) :
    ∃ m ∈ M, ∃ m' ∈ M', ∃ r : R, IsUnit r ∧ algebraMap R S r = m * m'
```

Let `S` be an `R`-algebra whose structure map is injective, and let `M` and `M'` be
`R`-submodules of `S`. Suppose every product `m m'` with `m ∈ M` and `m' ∈ M'` comes from
`R`, and the elements of `R` arising this way generate the unit ideal. Then a single such
product is the image of a unit of `R`.

*Proof.*

1. For every maximal ideal `P` there is a generator `r_P ∉ P`, with
   `algebraMap r_P = m_P m'_P` for some `m_P ∈ M` and `m'_P ∈ M'`. Otherwise every
   generator would lie in `P`, so their span `⊤` would be contained in `P`.
2. Choose separating elements `e_P` by `exists_separating`. Also choose `ρ(P, Q) ∈ R` with
   `algebraMap ρ(P, Q) = m_P m'_Q` (`hprod`).
3. Put `m = Σ_P e_P m_P ∈ M`, `m' = Σ_Q e_Q m'_Q ∈ M'` and
   `r = Σ_P Σ_Q e_P e_Q ρ(P, Q)`. Expanding the product shows that
   `algebraMap r = m m'`.
4. Suppose `r` is not a unit. Then `r` lies in some maximal ideal `N`
   (`exists_max_ideal_of_mem_nonunits`). Every term with `(P, Q) ≠ (N, N)` lies in `N`,
   because `P ≠ N` or `Q ≠ N` and `e_P` or `e_Q` then lies in `N`. So the remaining term
   `e_N e_N ρ(N, N)` lies in `N`. By injectivity of `algebraMap`, `ρ(N, N) = r_N`. Since
   `N` is prime, this contradicts `e_N ∉ N` and `r_N ∉ N`.
