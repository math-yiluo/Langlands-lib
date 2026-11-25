# The local counts at the places of `S`

`Langlands/GaloisCohomology/Global/Selmer/LocalCount.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `v` a finite place, `K_v = v.adicCompletion K` and `𝒪_v` its ring of
integers (`v.adicCompletionIntegers K`).

* The ring of integers `𝒪[K_v]` of the local field structure on `K_v` given by
  `Langlands.Global.FiniteCompletion.valuativeRel` is `𝒪_v` (`integer_eq_adicCompletionIntegers`), so
  that the quotients by an integer have the same order (`card_integer_quotient_natCast_eq`).
* **The product formula** in the form `∏_{v ∈ S} #(𝒪_v / m𝒪_v) = m^{[K : ℚ]}` for an integer `m ≥ 1`
  and a finite set `S` of finite places containing the places above `m`
  (`prod_card_quotient_natCast_eq` of the module
  `Langlands.ClassFieldTheory.Global.LocalPowerIndex`).
* **The local Euler characteristic** at `v` for a finite smooth module `M` of `G_S`:
  `#H¹(K_v, M) = #H⁰(K_v, M) · #H²(K_v, M) · #(𝒪_v / #M 𝒪_v)` (`card_cohomology_one_localModule`).

At a real place the corresponding statement is the Herbrand quotient `#H¹(K_w, M) = #H²(K_w, M)`
(`card_cohomology_one_eq_card_cohomology_two_of_isReal` of
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio`).

```lean
theorem integer_eq_adicCompletionIntegers :
    letI
theorem card_integer_quotient_natCast_eq (m : ℕ) :
    letI
theorem card_cohomology_one_localModule (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (cohomology (localModule ι M v) 1) =
      Nat.card (cohomology (localModule ι M v) 0) * Nat.card (cohomology (localModule ι M v) 2) *
        Nat.card (v.adicCompletionIntegers K ⧸
          Ideal.span {((Nat.card M : ℕ) : v.adicCompletionIntegers K)})
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.integer_eq_adicCompletionIntegers : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  Valuation.integer (ValuativeRel.valuation (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) =
    ValuationSubring.toSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
@Langlands.GaloisCohomology.card_integer_quotient_natCast_eq : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ),
  Nat.card
      (↥(Valuation.integer (ValuativeRel.valuation (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) ⧸
        Ideal.span {↑m}) =
    Nat.card (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) ⧸ Ideal.span {↑m})
@Langlands.GaloisCohomology.card_cohomology_one_localModule : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [Finite ↑M]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 1) =
    Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 0) *
        Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 2) *
      Nat.card (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) ⧸ Ideal.span {↑(Nat.card ↑M)})
```

## Outline of the proofs

- Both rings are `{x | v(x) ≤ 1}` in `K_v` (`Valuation.vle_one_iff`,
  `Langlands.Global.FiniteCompletion.valuativeRel_vle`, `mem_adicCompletionIntegers`).
- Product formula: `#(𝒪_v / m𝒪_v)` is the absolute norm of the `v`-part `v^{e_v}` of `m𝒪_K`
  (`Langlands.ClassFieldTheory.Global.card_quotient_eq_absNorm`, `residueIdeal_eq_pow`); the
  `v`-parts over `S` multiply to `m𝒪_K` because `S` contains every place where `e_v ≠ 0`
  (`Ideal.finprod_heightOneSpectrum_pow_multiplicity`), and `N(m𝒪_K) = |N_{K/ℚ}(m)| = m^{[K : ℚ]}`.
- Local Euler characteristic: `Langlands.GaloisCohomology.Local.card_cohomology_one` for the local
  field `K_v`, and the comparison of the rings of integers.

## Declarations

`integer_eq_adicCompletionIntegers`, `card_integer_quotient_natCast_eq`, `card_cohomology_one_localModule`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (7.3.1) (Tate's local Euler characteristic `χ(k, A) = ‖#A‖_k`), p. 392.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §2, Theorem 2.8, p. 31.
