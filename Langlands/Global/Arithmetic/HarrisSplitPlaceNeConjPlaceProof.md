# A place above a split imaginary quadratic prime differs from its conjugate

Module `Langlands.Global.Arithmetic.HarrisSplitPlaceNeConjPlaceProof`,
namespace `Langlands.Global.Harris`.

`Langlands.Global.Harris.splitPlaceNeConjPlace` proves the Library statement
`Langlands.Global.Harris.SplitPlaceNeConjPlaceStatement` (Statement 3 of
[HarrisAuxiliaryConjugatePairStatement](HarrisAuxiliaryConjugatePairStatement.md#3-splitplaceneconjplacestatement))
at universe `u`. The statement is not changed and has no extra premise.

The theorem covers every finite place `v` of a CM number field `E` that
contains `p`, not only places built from Harris data. Let `p` be a rational
prime and `K₀ ⊆ E` an intermediate field with
`IsSplitImaginaryQuadratic p K₀`: `[K₀ : ℚ] = 2`, `K₀` is totally complex,
and two distinct finite places `P ≠ Q` of `K₀` contain `p`. If
`(p : 𝓞 E) ∈ v.asIdeal`, then `v ≠ conjPlace E v`.

The proof follows the argument of §3 of the statement's Markdown, which is
derived from Harris (1998), Section 2, printed p.192 (source
`harris-1998-local-langlands`). Galois theory of `K₀/ℚ` replaces the explicit
quadratic-field calculation.

## Module contents

| Declaration | Content |
| --- | --- |
| `under_eq_span_of_natCast_mem` | A finite place `w` of a field `K` with `(p : 𝓞 K) ∈ w.asIdeal` satisfies `w.asIdeal.under ℤ = Ideal.span {(p : ℤ)}`. |
| `eq_of_conjPlace_eq_self` | In a CM field `K` with `finrank ℚ K = 2`, let `w` be a finite place above `p` with `conjPlace K w = w`. Then every finite place `P` above `p` equals `w`. |
| `splitPlaceNeConjPlace` | The target statement. |

All three are theorems; the module defines nothing.

## Implemented proof

### `under_eq_span_of_natCast_mem`

Since `p` is prime, `(p : ℤ)` is irreducible, so `Ideal.span {(p : ℤ)}` is a
maximal ideal of `ℤ` (`PrincipalIdealRing.isMaximal_of_irreducible`). It is
contained in `w.asIdeal.under ℤ`: the image of `(p : ℤ)` in `𝓞 K` is
`(p : 𝓞 K)` (`map_natCast`), and that element lies in `w.asIdeal`. The
contraction of the prime ideal `w.asIdeal` is prime, hence not `⊤`. By
maximality the two ideals are equal (`Ideal.IsMaximal.eq_of_le`).

### `eq_of_conjPlace_eq_self`

1. **The Galois group.** `finrank ℚ K = 2` gives
   `Algebra.IsQuadraticExtension ℚ K`. Mathlib's instance
   `Algebra.IsQuadraticExtension.isGalois` then makes `K/ℚ` Galois, since the
   characteristic is zero. So `Nat.card Gal(K/ℚ) = 2`
   (`IsGalois.card_aut_eq_finrank`), which is prime.
2. **Complex conjugation in the Galois group.** Let
   `τ = (IsCMField.complexConj K).restrictScalars ℚ`. Then `τ ≠ 1`: two
   automorphisms that agree as maps agree as automorphisms, so `τ = 1` would
   give `IsCMField.complexConj K = 1`, against
   `IsCMField.complexConj_ne_one`.
3. **`τ` fixes `w`.** The prime ideal of `conjPlace K w` is the preimage of
   `w.asIdeal` under complex conjugation on `𝓞 K` (`finitePlaceEquiv_mem`).
   On `𝓞 K`, the action `τ • x` of `Gal(K/ℚ)` is that conjugation by
   definition. So `conjPlace K w = w` says exactly that
   `τ • x ∈ w.asIdeal ↔ x ∈ w.asIdeal` for all `x : 𝓞 K`. With
   `Ideal.mem_pointwise_smul_iff_inv_smul_mem` and `smul_inv_smul`, this gives
   `τ • w.asIdeal = w.asIdeal`. So `τ` lies in the stabilizer of `w.asIdeal`
   for the pointwise action of `Gal(K/ℚ)` on ideals of `𝓞 K`.
4. **The whole group fixes `w`.** The group has prime order, so this
   stabilizer is `⊥` or `⊤` (`Subgroup.eq_bot_or_eq_top_of_prime_card`). It
   contains `τ ≠ 1`, so it is not `⊥`. Hence every `σ ∈ Gal(K/ℚ)` satisfies
   `σ • w.asIdeal = w.asIdeal`.
5. **Transitivity.** `w.asIdeal` and `P.asIdeal` have the same contraction
   `Ideal.span {(p : ℤ)}` to `ℤ`, by `under_eq_span_of_natCast_mem`.
   Mathlib's instances make `Gal(K/ℚ)` a Galois group of `𝓞 K` over `ℤ`
   (`IsGaloisGroup`). So `Algebra.IsInvariant.exists_smul_of_under_eq` gives
   `σ` with `P.asIdeal = σ • w.asIdeal`. By step 4 this is `w.asIdeal`, and
   `P = w` by `HeightOneSpectrum.ext`.

### `splitPlaceNeConjPlace`

Take `p`, `E`, `K₀`, `v` and the hypotheses
`⟨h2, hTC, P, Q, hPQ, hpP, hpQ⟩` and `(p : 𝓞 E) ∈ v.asIdeal`. Suppose
`v = conjPlace E v`.

1. **`K₀` as a CM field.** `h2` gives `Algebra.IsQuadraticExtension ℚ K₀`.
   `ℚ` is totally real and `K₀` is totally complex (`hTC`), so `K₀/ℚ` is a CM
   extension. `IsCMField.ofCMExtension ℚ K₀` makes `K₀` a CM field, with
   complex conjugation `IsCMField.complexConj K₀`. This instance is local to
   the proof.
2. **The place below `v`.** Let
   `w = HeightOneSpectrum.under (𝓞 K₀) v`, the finite place of `K₀` whose
   prime ideal is `v.asIdeal ∩ 𝓞 K₀`. It contains `(p : 𝓞 K₀)`, because the
   image of that element in `𝓞 E` is `(p : 𝓞 E) ∈ v.asIdeal`
   (`map_natCast`). By construction `v.asIdeal` lies over `w.asIdeal`.
3. **`w` is fixed by conjugation.**
   `HarrisDatum.conjPlace_liesOver w v` (module
   `Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof`)
   compares the two complex conjugations along `K₀ ⊆ E`
   (`HarrisDatum.complexConj_algebraMap`). It shows that the conjugate place
   `conjPlace E v` lies over `conjPlace K₀ w`. If `conjPlace K₀ w ≠ w`, then
   `HarrisDatum.ne_of_liesOver` gives `conjPlace E v ≠ v`, since places above
   distinct places are distinct. This contradicts the assumption. So
   `conjPlace K₀ w = w`.
4. **Conclusion.** `eq_of_conjPlace_eq_self` applies to `K₀` and `w`. It
   gives `P = w` and `Q = w`, so `P = Q`, contradicting `hPQ`.

The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Dependencies

- `Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement`: the
  target statement.
- `Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof`:
  `HarrisDatum.conjPlace_liesOver` and `HarrisDatum.ne_of_liesOver`.
- Mathlib: the module imports `Mathlib.NumberTheory.RamificationInertia.Galois`.
  The Mathlib results used are `Algebra.IsInvariant.exists_smul_of_under_eq`
  (`Mathlib.RingTheory.Invariant.Basic`), the CM-field API of
  `Mathlib.NumberTheory.NumberField.CMField` (`IsCMField.ofCMExtension`,
  `IsCMField.complexConj`, `IsCMField.complexConj_ne_one`), the
  `IsGaloisGroup` instances for rings of integers
  (`Mathlib.FieldTheory.Galois.IsGaloisGroup`),
  `Algebra.IsQuadraticExtension.isGalois` and `IsGalois.card_aut_eq_finrank`
  (`Mathlib.FieldTheory.Galois.Basic`),
  `Subgroup.eq_bot_or_eq_top_of_prime_card`
  (`Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup`) and
  `IsDedekindDomain.HeightOneSpectrum.under`
  (`Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`).
