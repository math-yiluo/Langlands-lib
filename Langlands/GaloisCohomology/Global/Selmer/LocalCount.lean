import Langlands.ClassFieldTheory.Global.LocalPowerIndex
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Main

/-!
# The local counts at the places of `S`

Let `K` be a number field, `v` a finite place, `K_v = v.adicCompletion K` and `𝒪_v` its ring of
integers. For use at the places of a finite set `S`:

* the ring of integers `𝒪[K_v]` of the local field structure on `K_v` given by
  `Langlands.Global.FiniteCompletion.valuativeRel` is `v.adicCompletionIntegers K`, so that the
  quotients by an integer have the same order (`card_integer_quotient_natCast_eq`);
* **the product formula** in the form `∏_{v ∈ S} #(𝒪_v / m𝒪_v) = m^{[K : ℚ]}` for `m ≥ 1` when `S`
  contains the places above `m` (`prod_card_quotient_natCast_eq` of
  `Langlands.ClassFieldTheory.Global.LocalPowerIndex`): `#(𝒪_v / m𝒪_v)` is the absolute
  norm of the `v`-part of `m𝒪_K`, the `v`-parts multiply to `m𝒪_K`, and `N(m𝒪_K) = m^{[K : ℚ]}`;
* **the local Euler characteristic** at `v` for a finite smooth module `M` of `G_S`:
  `#H¹(K_v, M) = #H⁰(K_v, M) · #H²(K_v, M) · #(𝒪_v / #M 𝒪_v)` (`card_cohomology_one_localModule`),
  from `Langlands.GaloisCohomology.Local.card_cohomology_one`;
* the Herbrand quotient at a real place, `#H¹(K_w, M) = #H²(K_w, M)`, is
  `card_cohomology_one_eq_card_cohomology_two_of_isReal` of
  `Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum ValuativeRel

universe u

noncomputable section

section Integers

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The ring of integers of the local field structure on `K_v` is `v.adicCompletionIntegers K`. -/
theorem integer_eq_adicCompletionIntegers :
    letI := Langlands.Global.FiniteCompletion.valuativeRel v
    (𝒪[v.adicCompletion K] : Subring (v.adicCompletion K)) =
      (v.adicCompletionIntegers K).toSubring := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  ext x
  change valuation (v.adicCompletion K) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers K
  rw [← Valuation.vle_one_iff, Langlands.Global.FiniteCompletion.valuativeRel_vle, map_one,
    mem_adicCompletionIntegers]

/-- `𝒪[K_v] / m` and `𝒪_v / m` have the same order. -/
theorem card_integer_quotient_natCast_eq (m : ℕ) :
    letI := Langlands.Global.FiniteCompletion.valuativeRel v
    Nat.card (𝒪[v.adicCompletion K] ⧸ Ideal.span {(m : 𝒪[v.adicCompletion K])}) =
      Nat.card (v.adicCompletionIntegers K ⧸
        Ideal.span {(m : v.adicCompletionIntegers K)}) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  let e := RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ e ?_).toEquiv
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

end Integers

section LocalEuler

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- **The local Euler characteristic** at a finite place:
`#H¹(K_v, M) = #H⁰(K_v, M) · #H²(K_v, M) · #(𝒪_v / #M 𝒪_v)`. -/
theorem card_cohomology_one_localModule (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (cohomology (localModule ι M v) 1) =
      Nat.card (cohomology (localModule ι M v) 0) * Nat.card (cohomology (localModule ι M v) 2) *
        Nat.card (v.adicCompletionIntegers K ⧸
          Ideal.span {((Nat.card M : ℕ) : v.adicCompletionIntegers K)}) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  have h := Local.card_cohomology_one (K := v.adicCompletion K)
    (Ksep := AlgebraicClosure (v.adicCompletion K)) (localModule ι M v)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  rw [h, card_integer_quotient_natCast_eq v]

end LocalEuler

end

end Langlands.GaloisCohomology
